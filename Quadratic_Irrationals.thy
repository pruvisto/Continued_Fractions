section \<open>Quadratic Irrationals\<close>
theory Quadratic_Irrationals
imports
  Continued_Fractions
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Library.Discrete"
begin

subsection \<open>Basic results on rationality of square roots\<close>

lemma inverse_in_Rats_iff [simp]: "inverse (x :: real) \<in> \<rat> \<longleftrightarrow> x \<in> \<rat>"
  by (auto simp: inverse_eq_divide divide_in_Rats_iff1)

lemma nonneg_sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a" and "x \<ge> 0"
  shows   "x \<in> \<nat> \<or> x \<notin> \<rat>"
proof safe
  assume "x \<notin> \<nat>" and "x \<in> \<rat>"
  from Rats_abs_nat_div_natE[OF this(2)]
    obtain p q :: nat where q_nz [simp]: "q \<noteq> 0" and "abs x = p / q" and coprime: "coprime p q" .
  with \<open>x \<ge> 0\<close> have x: "x = p / q"
      by simp
  with assms have "real (q ^ 2) * real a = real (p ^ 2)"
    by (simp add: field_simps)
  also have "real (q ^ 2) * real a = real (q ^ 2 * a)"
    by simp
  finally have "p ^ 2 = q ^ 2 * a"
    by (subst (asm) of_nat_eq_iff) auto
  hence "q ^ 2 dvd p ^ 2"
    by simp
  hence "q dvd p"
    by simp
  with coprime have "q = 1"
    by auto
  with x and \<open>x \<notin> \<nat>\<close> show False
    by simp
qed

text \<open>
  A square root of a natural number is either an integer or irrational.
\<close>
corollary sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a"
  shows   "x \<in> \<int> \<or> x \<notin> \<rat>"
proof (cases "x \<ge> 0")
  case True
  with nonneg_sqrt_nat_or_irrat[OF assms this]
    show ?thesis by (auto simp: Nats_altdef2)
next
  case False
  from assms have "(-x) ^ 2 = real a"
    by simp
  moreover from False have "-x \<ge> 0"
    by simp
  ultimately have "-x \<in> \<nat> \<or> -x \<notin> \<rat>"
    by (rule nonneg_sqrt_nat_or_irrat)
  thus ?thesis
    by (auto simp: Nats_altdef2 minus_in_Ints_iff)
qed

corollary sqrt_nat_or_irrat':
  "sqrt (real a) \<in> \<nat> \<or> sqrt (real a) \<notin> \<rat>"
  using nonneg_sqrt_nat_or_irrat[of "sqrt a" a] by auto

text \<open>
  The square root of a natural number \<open>n\<close> is again a natural number iff \<open>n is a perfect square.\<close>
\<close>
corollary sqrt_nat_iff_is_square:
  "sqrt (real n) \<in> \<nat> \<longleftrightarrow> is_square n"
proof
  assume "sqrt (real n) \<in> \<nat>"
  then obtain k where "sqrt (real n) = real k" by (auto elim!: Nats_cases)
  hence "sqrt (real n) ^ 2 = real (k ^ 2)" by (simp only: of_nat_power)
  also have "sqrt (real n) ^ 2 = real n" by simp
  finally have "n = k ^ 2" by (simp only: of_nat_eq_iff)
  thus "is_square n" by blast
qed (auto elim!: is_nth_powerE)

corollary irrat_sqrt_nonsquare: "\<not>is_square n \<Longrightarrow> sqrt (real n) \<notin> \<rat>"
  using sqrt_nat_or_irrat'[of n] by (auto simp: sqrt_nat_iff_is_square)

lemma sqrt_of_nat_in_Rats_iff: "sqrt (real n) \<in> \<rat> \<longleftrightarrow> is_square n"
  using irrat_sqrt_nonsquare[of n] sqrt_nat_iff_is_square[of n] Nats_subset_Rats by blast

lemma Discrete_sqrt_altdef: "Discrete.sqrt n = nat \<lfloor>sqrt n\<rfloor>"
proof -
  have "real (Discrete.sqrt n ^ 2) \<le> sqrt n ^ 2"
    by simp
  hence "Discrete.sqrt n \<le> sqrt n"
    unfolding of_nat_power by (rule power2_le_imp_le) auto
  moreover have "real (Suc (Discrete.sqrt n) ^ 2) > real n"
    unfolding of_nat_less_iff by (rule Suc_sqrt_power2_gt)
  hence "real (Discrete.sqrt n + 1) ^ 2 > sqrt n ^ 2"
    unfolding of_nat_power by simp
  hence "real (Discrete.sqrt n + 1) > sqrt n"
    by (rule power2_less_imp_less) auto
  hence "Discrete.sqrt n + 1 > sqrt n" by simp
  ultimately show ?thesis by linarith
qed


subsection \<open>Quadratic irrationals\<close>

text \<open>
  Irrational real numbers $x$ that satisfy a quadratic equation $a x^2 + b x + c = 0$
  with \<open>a\<close>, \<open>b\<close>, \<open>c\<close> not all equal to 0 are called \<^emph>\<open>quadratic irrationals\<close>. These are of the form
  $p + q \sqrt{d}$ for rational numbers \<open>p\<close>, \<open>q\<close> and a positive integer \<open>d\<close>.
\<close>
inductive quadratic_irrational :: "real \<Rightarrow> bool" where
  "x \<notin> \<rat> \<Longrightarrow> real_of_int a * x ^ 2 + real_of_int b * x + real_of_int c = 0 \<Longrightarrow>
     a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0 \<Longrightarrow> quadratic_irrational x"

lemma quadratic_irrational_sqrt [intro]:
  assumes "\<not>is_square n"
  shows   "quadratic_irrational (sqrt (real n))"
  using irrat_sqrt_nonsquare[OF assms]
  by (intro quadratic_irrational.intros[of "sqrt n" 1 0 "-int n"]) auto

lemma quadratic_irrational_uminus [intro]:
  assumes "quadratic_irrational x"
  shows   "quadratic_irrational (-x)"
  using assms
proof induction
  case (1 x a b c)
  thus ?case by (intro quadratic_irrational.intros[of "-x" a "-b" c]) auto
qed

lemma quadratic_irrational_uminus_iff [simp]:
  "quadratic_irrational (-x) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_uminus[of x] quadratic_irrational_uminus[of "-x"] by auto

lemma quadratic_irrational_plus_int [intro]:
  assumes "quadratic_irrational x"
  shows   "quadratic_irrational (x + of_int n)"
  using assms
proof induction
  case (1 x a b c)
  define x' where "x' = x + of_int n"
  define a' b' c' where
     "a' = a" and "b' = b - 2 * of_int n * a" and
     "c' = a * of_int n ^ 2 - b * of_int n + c"
  from 1 have "0 = a * (x' - of_int n) ^ 2 + b * (x' - of_int n) + c"
    by (simp add: x'_def)
  also have "\<dots> = a' * x' ^ 2 + b' * x' + c'"
    by (simp add: algebra_simps a'_def b'_def c'_def power2_eq_square)
  finally have "\<dots> = 0" ..
  moreover have "x' \<notin> \<rat>"
    using 1 by (auto simp: x'_def add_in_Rats_iff2)
  moreover have "a' \<noteq> 0 \<or> b' \<noteq> 0 \<or> c' \<noteq> 0"
    using 1 by (auto simp: a'_def b'_def c'_def)
  ultimately show ?case
    by (intro quadratic_irrational.intros[of "x + of_int n" a' b' c']) (auto simp: x'_def)
qed

lemma quadratic_irrational_plus_int_iff [simp]:
  "quadratic_irrational (x + of_int n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int[of x n]
        quadratic_irrational_plus_int[of "x + of_int n" "-n"] by auto

lemma quadratic_irrational_minus_int_iff [simp]:
  "quadratic_irrational (x - of_int n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "-n"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_plus_nat_iff [simp]:
  "quadratic_irrational (x + of_nat n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "int n"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_minus_nat_iff [simp]:
  "quadratic_irrational (x - of_nat n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "-int n"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_plus_1_iff [simp]:
  "quadratic_irrational (x + 1) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x 1]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_minus_1_iff [simp]:
  "quadratic_irrational (x - 1) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "-1"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_plus_numeral_iff [simp]:
  "quadratic_irrational (x + numeral n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "numeral n"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_minus_numeral_iff [simp]:
  "quadratic_irrational (x - numeral n) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_plus_int_iff[of x "-numeral n"]
  by (simp del: quadratic_irrational_plus_int_iff)

lemma quadratic_irrational_inverse:
  assumes "quadratic_irrational x"
  shows   "quadratic_irrational (inverse x)"
  using assms
proof induction
  case (1 x a b c)
  from 1 have "x \<noteq> 0" by auto
  have "0 = (real_of_int a * x\<^sup>2 + real_of_int b * x + real_of_int c) / x ^ 2"
    by (subst 1) simp
  also have "\<dots> = real_of_int c * (inverse x) ^ 2 + real_of_int b * inverse x + real_of_int a"
    using \<open>x \<noteq> 0\<close> by (simp add: field_simps power2_eq_square)
  finally have "\<dots> = 0" ..
  thus ?case using 1
    by (intro quadratic_irrational.intros[of "inverse x" c b a]) auto
qed

lemma quadratic_irrational_inverse_iff [simp]:
  "quadratic_irrational (inverse x) \<longleftrightarrow> quadratic_irrational x"
  using quadratic_irrational_inverse[of x] quadratic_irrational_inverse[of "inverse x"]
  by (cases "x = 0") auto

lemma quadratic_irrational_cfrac_remainder_iff:
  "quadratic_irrational (cfrac_remainder c n) \<longleftrightarrow> quadratic_irrational (cfrac_lim c)"
proof (cases "cfrac_length c = \<infinity>")
  case False
  thus ?thesis
    by (auto simp: quadratic_irrational.simps)
next
  case [simp]: True
  show ?thesis
  proof (induction n)
    case (Suc n)
    from Suc.prems have "cfrac_remainder c (Suc n) =
                           inverse (cfrac_remainder c n - of_int (cfrac_nth c n))"
      by (subst cfrac_remainder_Suc) (auto simp: field_simps)
    also have "quadratic_irrational \<dots> \<longleftrightarrow> quadratic_irrational (cfrac_remainder c n)"
      by simp
    also have "\<dots> \<longleftrightarrow> quadratic_irrational (cfrac_lim c)"
      by (rule Suc.IH)
    finally show ?case .
  qed auto
qed
                
subsection \<open>Real solutions of quadratic equations\<close>

text \<open>
  For the next result, we need some basic properties of real solutions to quadratic equations.
\<close>
lemma quadratic_equation_reals_cases:
  fixes a b c :: real
  defines "f \<equiv> (\<lambda>x. a * x ^ 2 + b * x + c)"
  defines "discr \<equiv> (b^2 - 4 * a * c)"
  shows   "{x. f x = 0} =
             (if a = 0 then
                (if b = 0 then if c = 0 then UNIV else {} else {-c/b})
              else if discr \<ge> 0 then {(-b + sqrt discr) / (2 * a), (-b - sqrt discr) / (2 * a)}
                                else {})" (is ?th1)                
proof (cases "a = 0")
  case [simp]: True
  show ?th1
  proof (cases "b = 0")
    case [simp]: True
    hence "{x. f x = 0} = (if c = 0 then UNIV else {})"
      by (auto simp: f_def)
    thus ?th1 by simp
  next
    case False
    hence "{x. f x = 0} = {-c / b}" by (auto simp: f_def field_simps)
    thus ?th1 using False by simp
  qed
next
  case [simp]: False
  show ?th1
  proof (cases "discr \<ge> 0")
    case True
    {
      fix x :: real
      have "f x = a * (x - (-b + sqrt discr) / (2 * a)) * (x - (-b - sqrt discr) / (2 * a))"
        using True by (simp add: f_def field_simps discr_def power2_eq_square)
      also have "\<dots> = 0 \<longleftrightarrow> x \<in> {(-b + sqrt discr) / (2 * a), (-b - sqrt discr) / (2 * a)}"
        by simp
      finally have "f x = 0 \<longleftrightarrow> \<dots>" .
    }
    hence "{x. f x = 0} = {(-b + sqrt discr) / (2 * a), (-b - sqrt discr) / (2 * a)}"
      by blast
    thus ?th1 using True by simp
  next
    case False
    {
      fix x :: real
      assume x: "f x = 0"
      have "0 \<le> (x + b / (2 * a)) ^ 2" by simp
      also have "f x = a * ((x + b / (2 * a)) ^ 2 - b ^ 2 / (4 * a ^ 2) + c / a)"
        by (simp add: field_simps power2_eq_square f_def)
      with x have "(x + b / (2 * a)) ^ 2 - b ^ 2 / (4 * a ^ 2) + c / a = 0"
        by simp
      hence "(x + b / (2 * a)) ^ 2 = b ^ 2 / (4 * a ^ 2) - c / a"
        by (simp add: algebra_simps)
      finally have "0 \<le> (b\<^sup>2 / (4 * a\<^sup>2) - c / a) * (4 * a\<^sup>2)"
        by (intro mult_nonneg_nonneg) auto
      also have "\<dots> = b\<^sup>2 - 4 * a * c" by (simp add: field_simps power2_eq_square)
      also have "\<dots> < 0" using False by (simp add: discr_def)
      finally have False by simp
    }
    hence "{x. f x = 0} = {}" by auto
    thus ?th1 using False by simp
  qed
qed

lemma finite_quadratic_equation_solutions_reals:
  fixes a b c :: real
  defines "discr \<equiv> (b^2 - 4 * a * c)"
  shows   "finite {x. a * x ^ 2 + b * x + c = 0} \<longleftrightarrow> a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0"
  by (subst quadratic_equation_reals_cases)
     (auto simp: discr_def card_eq_0_iff infinite_UNIV_char_0 split: if_split)

lemma card_quadratic_equation_solutions_reals:
  fixes a b c :: real
  defines "discr \<equiv> (b^2 - 4 * a * c)"
  shows   "card {x. a * x ^ 2 + b * x + c = 0} =
             (if a = 0 then
                (if b = 0 then 0 else 1)
              else if discr \<ge> 0 then if discr = 0 then 1 else 2 else 0)" (is ?th1)                
  by (subst quadratic_equation_reals_cases)
     (auto simp: discr_def card_eq_0_iff infinite_UNIV_char_0 split: if_split)

lemma card_quadratic_equation_solutions_reals_le_2:
  "card {x :: real. a * x ^ 2 + b * x + c = 0} \<le> 2"
  by (subst card_quadratic_equation_solutions_reals) auto

lemma quadratic_equation_solution_rat_iff:
  fixes a b c :: int and x y :: real
  defines "f \<equiv> (\<lambda>x::real. a * x ^ 2 + b * x + c)"
  defines "discr \<equiv> nat (b ^ 2 - 4 * a * c)"
  assumes "a \<noteq> 0" "f x = 0"
  shows   "x \<in> \<rat> \<longleftrightarrow> is_square discr"
proof -
  define discr' where "discr' \<equiv> real_of_int (b ^ 2 - 4 * a * c)"
  from assms have "x \<in> {x. f x = 0}" by simp
  with \<open>a \<noteq> 0\<close> have "discr' \<ge> 0" unfolding discr'_def f_def of_nat_diff
    by (subst (asm) quadratic_equation_reals_cases) (auto simp: discr_def split: if_splits)
  hence *: "sqrt (discr') = sqrt (real discr)" unfolding of_int_0_le_iff discr_def discr'_def
    by (simp add: algebra_simps nat_diff_distrib)
  from \<open>x \<in> {x. f x = 0}\<close> have "x = (-b + sqrt discr) / (2 * a) \<or> x = (-b - sqrt discr) / (2 * a)"
    using \<open>a \<noteq> 0\<close> * unfolding discr'_def f_def
    by (subst (asm) quadratic_equation_reals_cases) (auto split: if_splits)
  thus ?thesis using \<open>a \<noteq> 0\<close>
    by (auto simp: sqrt_of_nat_in_Rats_iff divide_in_Rats_iff2 diff_in_Rats_iff2 diff_in_Rats_iff1)
qed


subsection \<open>Periodic continued fractions and quadratic irrationals\<close>

text \<open>
  We now show the main result: A positive irrational number has a periodic continued 
  fraction expansion iff it is a quadratic irrational.

  In principle, this statement naturally also holds for negative numbers, but the current 
  formalisation of continued fractions only supports non-negative numbers. It also holds for
  rational numbers in some sense, since their continued fraction expansion is finite to begin with.
\<close>
theorem periodic_cfrac_imp_quadratic_irrational:
  assumes [simp]: "cfrac_length c = \<infinity>"
      and period: "l > 0" "\<And>k. k \<ge> N \<Longrightarrow> cfrac_nth c (k + l) = cfrac_nth c k"
  shows   "quadratic_irrational (cfrac_lim c)"
proof -
  define h' and k' where "h' = conv_num_int (cfrac_drop N c)" 
                     and "k' = conv_denom_int (cfrac_drop N c)"
  define x' where "x' = cfrac_remainder c N"

  have c_pos: "cfrac_nth c n > 0" if "n \<ge> N" for n
  proof -
    from assms(1,2) have "cfrac_nth c (n + l) > 0" by auto
    with assms(3)[OF that] show ?thesis by simp
  qed
  have k'_pos: "k' n > 0" if "n \<noteq> -1" "n \<ge> -2" for n
    using that by (auto simp: k'_def conv_denom_int_def intro!: conv_denom_pos)
  have k'_nonneg: "k' n \<ge> 0" if "n \<ge> -2" for n
    using that by (auto simp: k'_def conv_denom_int_def intro!: conv_denom_pos)
  have "cfrac_nth c (n + (N + l)) = cfrac_nth c (n + N)" for n
    using period(2)[of "n + N"] by (simp add: add_ac)
  have "cfrac_drop (N + l) c = cfrac_drop N c"
    by (rule cfrac_eqI) (use period(2)[of "n + N" for n] in \<open>auto simp: algebra_simps\<close>)
  hence x'_altdef: "x' = cfrac_remainder c (N + l)"
    by (simp add: x'_def cfrac_remainder_def)
  have x'_pos: "x' > 0" unfolding x'_def
    using c_pos by (intro cfrac_remainder_pos) auto

  define A where "A = (k' (int l - 1))"
  define B where "B = k' (int l - 2) - h' (int l - 1)"
  define C where "C = -(h' (int l - 2))"

  have pos: "(k' (int l - 1) * x' + k' (int l - 2)) > 0"
    using x'_pos \<open>l > 0\<close>
    by (intro add_pos_nonneg mult_pos_pos) (auto intro!: k'_pos k'_nonneg)
  have "x' = conv' (cfrac_drop N c) l x'"
    apply (subst x'_def, subst x'_altdef, subst add.commute)
    apply (simp add: cfrac_remainder_def cfrac_drop_add conv'_cfrac_remainder)
    apply (subst (2) cfrac_remainder_def [symmetric])
    apply (subst conv'_cfrac_remainder)
     apply auto
    done
  also have "\<dots> = (h' (int l - 1) * x' + h' (int l - 2)) / (k' (int l - 1) * x' + k' (int l - 2))"
    using conv'_num_denom_int[OF x'_pos, of _ l] unfolding h'_def k'_def
    by (simp add: mult_ac)
  finally have "x' * (k' (int l - 1) * x' + k' (int l - 2)) = (h' (int l - 1) * x' + h' (int l - 2))"
    using pos by (simp add: divide_simps)
  hence quadratic: "A * x' ^ 2 + B * x' + C = 0"
    by (simp add: algebra_simps power2_eq_square A_def B_def C_def)
  moreover have "x' \<notin> \<rat>" unfolding x'_def
    by auto
  moreover have "A > 0" using \<open>l > 0\<close> by (auto simp: A_def intro!: k'_pos)
  ultimately have "quadratic_irrational x'" using \<open>x' \<notin> \<rat>\<close>
    by (intro quadratic_irrational.intros[of x' A B C]) simp_all
  thus ?thesis
    using assms by (simp add: x'_def quadratic_irrational_cfrac_remainder_iff)
qed

theorem quadratic_irrational_imp_periodic_cfrac:
  assumes "quadratic_irrational (cfrac_lim e)"
  obtains N l where "l > 0" and "\<And>n m. n \<ge> N \<Longrightarrow> cfrac_nth e (n + m * l) = cfrac_nth e n"
                and "cfrac_remainder e (N + l) = cfrac_remainder e N"
proof -
  have [simp]: "cfrac_length e = \<infinity>"
    using assms by (auto simp: quadratic_irrational.simps)
  note [intro] = assms(1)
  define x where "x = cfrac_lim e"
  from assms obtain a b c :: int where
    nontrivial: "a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0" and
          root: "a * x^2 + b * x + c = 0" (is "?f x = 0")
    by (auto simp: quadratic_irrational.simps x_def)

  define f where "f = ?f"
  define h and k where "h = conv_num e" and "k = conv_denom e"
  define X where "X = cfrac_remainder e"
  have [simp]: "k i > 0" "k i \<noteq> 0" for i
    using conv_denom_pos[of e i] by (auto simp: k_def)
  have k_leI: "k i \<le> k j" if "i \<le> j" for i j
    by (auto simp: k_def intro!: conv_denom_leI that)
  have k_nonneg: "k n \<ge> 0" for n
    by (auto simp: k_def)
  have k_ge_1: "k n \<ge> 1" for n
    using k_leI[of 0 n] by (simp add: k_def)
    
  define R where "R = conv e"
  define A where "A = (\<lambda>n. a * h (n - 1) ^ 2 + b * h (n - 1) * k (n - 1) + c * k (n - 1) ^ 2)"
  define B where "B = (\<lambda>n. 2 * a * h (n - 1) * h (n - 2) + b * (h (n - 1) * k (n - 2) + h (n - 2) * k (n - 1)) + 2 * c * k (n - 1) * k (n - 2))"
  define C where "C = (\<lambda>n. a * h (n - 2) ^ 2 + b * h (n - 2) * k (n - 2) + c * k (n - 2) ^ 2)"

  define A' where "A' = nat \<lfloor>2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>a\<bar> + \<bar>b\<bar>\<rfloor>"
  define B' where "B' = nat \<lfloor>(3 / 2) * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + 9 / 4 * \<bar>a\<bar>\<rfloor>"

  have [simp]: "X n \<notin> \<rat>" for n unfolding X_def
    by simp
  from this[of 0] have [simp]: "x \<notin> \<rat>"
    unfolding X_def by (simp add: x_def)

  have "a \<noteq> 0"
  proof
    assume "a = 0"
    with root and nontrivial have "x = 0 \<or> x = -c / b"
      by (auto simp: divide_simps add_eq_0_iff)
    hence "x \<in> \<rat>" by (auto simp del: \<open>x \<notin> \<rat>\<close>)
    thus False by simp
  qed

  have bounds: "(A n, B n, C n) \<in> {-A'..A'} \<times> {-B'..B'} \<times> {-A'..A'}"
   and X_root: "A n * X n ^ 2 + B n * X n + C n = 0" if n: "n \<ge> 2" for n
  proof -
    define n' where "n' = n - 2"
    have n': "n = Suc (Suc n')" using \<open>n \<ge> 2\<close> unfolding n'_def by simp
    have *: "of_int (k (n - Suc 0)) * X n + of_int (k (n - 2)) \<noteq> 0"
    proof
      assume "of_int (k (n - Suc 0)) * X n + of_int (k (n - 2)) = 0"
      hence "X n = -k (n - 2) / k (n - 1)" by (auto simp: divide_simps mult_ac)
      also have "\<dots> \<in> \<rat>" by auto
      finally show False by simp
    qed
  
    let ?denom = "(k (n - 1) * X n + k (n - 2))"
    have "0 = 0 * ?denom ^ 2" by simp
    also have "0 * ?denom ^ 2 = (a * x ^ 2 + b * x + c) * ?denom ^ 2" using root by simp
    also have "\<dots> = a * (x * ?denom) ^ 2 + b * ?denom * (x * ?denom) + c * ?denom * ?denom"
      by (simp add: algebra_simps power2_eq_square)
    also have "x * ?denom = h (n - 1) * X n + h (n - 2)"
      using cfrac_lim_eq_num_denom_remainder_aux[of "n - 2" e] \<open>n \<ge> 2\<close>
      by (simp add: numeral_2_eq_2 Suc_diff_Suc x_def k_def h_def X_def)
    also have "a * \<dots> ^ 2 + b * ?denom * \<dots> + c * ?denom * ?denom = A n * X n ^ 2 + B n * X n + C n"
      by (simp add: A_def B_def C_def power2_eq_square algebra_simps)
    finally show "A n * X n ^ 2 + B n * X n + C n = 0" ..
  
    have f_abs_bound: "\<bar>f (R n)\<bar> \<le> (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) * (1 / (k n * k (Suc n))) +
                                      \<bar>a\<bar> * (1 / (k n * k (Suc n))) ^ 2" for n
    proof -
      have "\<bar>f (R n)\<bar> = \<bar>?f (R n) - ?f x\<bar>" by (simp add: root f_def)
      also have "?f (R n) - ?f x = (R n - x) * (2 * a * x + b) + (R n - x) ^ 2 * a"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<bar>\<dots>\<bar> \<le> \<bar>(R n - x) * (2 * a * x + b)\<bar> + \<bar>(R n - x) ^ 2 * a\<bar>"
        by (rule abs_triangle_ineq)
      also have "\<dots> = \<bar>2 * a * x + b\<bar> * \<bar>R n - x\<bar> + \<bar>a\<bar> * \<bar>R n - x\<bar> ^ 2"
        by (simp add: abs_mult)
      also have "\<dots> \<le> \<bar>2 * a * x + b\<bar> * (1 / (k n * k (Suc n))) + \<bar>a\<bar> * (1 / (k n * k (Suc n))) ^ 2"
        unfolding x_def R_def using cfrac_lim_minus_conv_bounds[of n e]
        by (intro add_mono mult_left_mono power_mono) (auto simp: k_def)
      also have "\<bar>2 * a * x + b\<bar> \<le> 2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>"
        by (rule order.trans[OF abs_triangle_ineq]) (auto simp: abs_mult)
      hence "\<bar>2 * a * x + b\<bar> * (1 / (k n * k (Suc n))) + \<bar>a\<bar> * (1 / (k n * k (Suc n))) ^ 2 \<le>
               \<dots> * (1 / (k n * k (Suc n))) + \<bar>a\<bar> * (1 / (k n * k (Suc n))) ^ 2"
        by (intro add_mono mult_right_mono) (auto intro!: mult_nonneg_nonneg k_nonneg)
      finally show "\<bar>f (R n)\<bar> \<le> \<dots>"
        by (simp add: mult_right_mono add_mono divide_left_mono)
    qed
  
    have h_eq_conv_k: "h i = R i * k i" for i
      using conv_denom_pos[of e i] unfolding R_def
      by (subst conv_num_denom) (auto simp: h_def k_def)
  
    have "A n = k (n - 1) ^ 2 * f (R (n - 1))" for n
      by (simp add: algebra_simps A_def n' k_def power2_eq_square h_eq_conv_k f_def)
    have A_bound: "\<bar>A i\<bar> \<le> A'" if "i > 0" for i
    proof -
      have "k i > 0"
        by simp
      hence "k i \<ge> 1"
        by linarith
      have "A i = k (i - 1) ^ 2 * f (R (i - 1))"
        by (simp add: algebra_simps A_def k_def power2_eq_square h_eq_conv_k f_def)
      also have "\<bar>\<dots>\<bar> = k (i - 1) ^ 2 * \<bar>f (R (i - 1))\<bar>"
        by (simp add: abs_mult f_def)
      also have "\<dots> \<le> k (i - 1) ^ 2 * ((2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) * (1 / (k (i - 1) * k (Suc (i - 1)))) +
                        \<bar>a\<bar> * (1 / (k (i - 1) * k (Suc (i - 1)))) ^ 2)"
        by (intro mult_left_mono f_abs_bound) auto
      also have "\<dots> = k (i - 1) / k i * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + \<bar>a\<bar> / k i ^ 2" using \<open>i > 0\<close>
        by (simp add: power2_eq_square field_simps)
      also have "\<dots> \<le> 1 * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + \<bar>a\<bar> / 1" using \<open>i > 0\<close> \<open>k i \<ge> 1\<close>
        by (intro add_mono divide_left_mono mult_right_mono)
           (auto intro!: k_leI one_le_power simp: of_nat_ge_1_iff)
      also have "\<dots> = 2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>a\<bar> + \<bar>b\<bar>" by simp
      finally show ?thesis unfolding A'_def by linarith
    qed
  
    have "C n = A (n - 1)" by (simp add: A_def C_def n')
    hence C_bound: "\<bar>C n\<bar> \<le> A'" using A_bound[of "n - 1"] n by simp
  
    have "B n = k (n - 1) * k (n - 2) *
                  (f (R (n - 1)) + f (R (n - 2)) - a * (R (n - 1) - R (n - 2)) ^ 2)"
      by (simp add: B_def h_eq_conv_k algebra_simps power2_eq_square f_def)
    also have "\<bar>\<dots>\<bar> = k (n - 1) * k (n - 2) * 
                       \<bar>f (R (n - 1)) + f (R (n - 2)) - a * (R (n - 1) - R (n - 2)) ^ 2\<bar>"
      by (simp add: abs_mult k_nonneg)
    also have "\<dots> \<le> k (n - 1) * k (n - 2) * 
                      (((2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) * (1 / (k (n - 1) * k (Suc (n - 1)))) +
                          \<bar>a\<bar> * (1 / (k (n - 1) * k (Suc (n - 1)))) ^ 2) +                      
                       ((2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) * (1 / (k (n - 2) * k (Suc (n - 2)))) +
                          \<bar>a\<bar> * (1 / (k (n - 2) * k (Suc (n - 2)))) ^ 2) +
                        \<bar>a\<bar> * \<bar>R (Suc (n - 2)) - R (n - 2)\<bar> ^ 2)" (is "_ \<le> _ * (?S1 + ?S2 + ?S3)")
      by (intro mult_left_mono order.trans[OF abs_triangle_ineq4] order.trans[OF abs_triangle_ineq] 
            add_mono f_abs_bound order.refl)
         (insert n, auto simp: abs_mult Suc_diff_Suc numeral_2_eq_2 k_nonneg)
    also have "\<bar>R (Suc (n - 2)) - R (n - 2)\<bar> = 1 / (k (n - 2) * k (Suc (n - 2)))"
      unfolding R_def k_def by (rule abs_diff_successive_convs)
    also have "of_int (k (n - 1) * k (n - 2)) * (?S1 + ?S2 + \<bar>a\<bar> * \<dots> ^ 2) = 
                 (k (n - 2) / k n + 1) * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + 
                 \<bar>a\<bar> * (k (n - 2) / (k (n - 1) * k n ^ 2) + 2 / (k (n - 1) * k (n - 2)))"
      (is "_ = ?S") using n by (simp add: field_simps power2_eq_square numeral_2_eq_2 Suc_diff_Suc)
    also {
      have A: "2 * real_of_int (k (n - 2)) \<le> of_int (k n)"
        using conv_denom_plus2_ratio_ge[of e "n - 2"] n
        by (simp add: numeral_2_eq_2 Suc_diff_Suc k_def)
      have "fib (Suc 2) \<le> k 2" unfolding k_def by (intro conv_denom_lower_bound)
      also have "\<dots> \<le> k n" by (intro k_leI n)
      finally have "k n \<ge> 2" by (simp add: numeral_3_eq_3)
      hence B: "of_int (k (n - 2)) * 2 ^ 2 \<le> (of_int (k (n - 1)) * (of_int (k n))\<^sup>2 :: real)"
        by (intro mult_mono power_mono) (auto intro: k_leI k_nonneg)
      have C: "1 * 1 \<le> real_of_int (k (n - 1)) * of_int (k (n - 2))" using k_ge_1
        by (intro mult_mono) (auto simp: Suc_le_eq of_nat_ge_1_iff k_nonneg)
      note A B C
    }
    hence "?S \<le> (1 / 2 + 1) * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + \<bar>a\<bar> * (1 / 4 + 2)"
      by (intro add_mono mult_right_mono mult_left_mono) (auto simp: field_simps)
    also have "\<dots> = (3 / 2) * (2 * \<bar>a\<bar> * \<bar>x\<bar> + \<bar>b\<bar>) + 9 / 4 * \<bar>a\<bar>" by simp
    finally have B_bound: "\<bar>B n\<bar> \<le> B'" unfolding B'_def by linarith
    from A_bound[of n] B_bound C_bound n
    show "(A n, B n, C n) \<in> {-A'..A'} \<times> {-B'..B'} \<times> {-A'..A'}" by auto
  qed

  have A_nz: "A n \<noteq> 0" if "n \<ge> 1" for n
    using that
  proof (induction n rule: dec_induct)
    case base
    show ?case
    proof
      assume "A 1 = 0"
      hence "real_of_int (A 1) = 0" by simp
      also have "real_of_int (A 1) =
                   real_of_int a * of_int (cfrac_nth e 0) ^ 2 +
                   real_of_int b * cfrac_nth e 0 + real_of_int c"
        by (simp add: A_def h_def k_def)
      finally have root': "\<dots> = 0" .

      have "cfrac_nth e 0 \<in> \<rat>" by auto
      also from root' and \<open>a \<noteq> 0\<close> have "?this \<longleftrightarrow> is_square (nat (b\<^sup>2 - 4 * a * c))"
        by (intro quadratic_equation_solution_rat_iff) auto
      also from root and \<open>a \<noteq> 0\<close> have "\<dots> \<longleftrightarrow> x \<in> \<rat>"
        by (intro quadratic_equation_solution_rat_iff [symmetric]) auto
      finally show False using \<open>x \<notin> \<rat>\<close> by contradiction
    qed
  next
    case (step m)
    hence nz: "C (Suc m) \<noteq> 0" by (simp add: C_def A_def)
    show "A (Suc m) \<noteq> 0"
    proof
      assume [simp]: "A (Suc m) = 0"
      have "X (Suc m) > 0" unfolding X_def
        by (intro cfrac_remainder_pos) auto
      with X_root[of "Suc m"] step.hyps nz have "X (Suc m) = -C (Suc m) / B (Suc m)"
        by (auto simp: divide_simps mult_ac)
      also have "\<dots> \<in> \<rat>" by auto
      finally show False by simp
    qed
  qed 

  have "finite ({-A'..A'} \<times> {-B'..B'} \<times> {-A'..A'})" by auto
  from this and bounds have "finite ((\<lambda>n. (A n, B n, C n)) ` {2..})"
    by (blast intro: finite_subset)
  moreover have "infinite ({2..} :: nat set)" by (simp add: infinite_Ici)
  ultimately have "\<exists>k1\<in>{2..}. infinite {n \<in> {2..}. (A n, B n, C n) = (A k1, B k1, C k1)}"
    by (intro pigeonhole_infinite)
  then obtain k0 where k0: "k0 \<ge> 2" "infinite {n \<in> {2..}. (A n, B n, C n) = (A k0, B k0, C k0)}"
    by auto
  from infinite_countable_subset[OF this(2)] obtain g :: "nat \<Rightarrow> _"
    where g: "inj g" "range g \<subseteq> {n\<in>{2..}. (A n, B n, C n) = (A k0, B k0, C k0)}" by blast
  hence g_ge_2: "g k \<ge> 2" for k by auto
  from g have [simp]: "A (g k) = A k0" "B (g k) = B k0" "C (g k) = C k0" for k
    by auto

  from g(1) have [simp]: "g k1 = g k2 \<longleftrightarrow> k1 = k2" for k1 k2 by (auto simp: inj_def)
  define z where "z = (A k0, B k0, C k0)"
  let ?h = "\<lambda>k. (A (g k), B (g k), C (g k))"
  from g have g': "distinct [g 1, g 2, g 3]" "?h 0 = z" "?h 1 = z" "?h 2 = z"
    by (auto simp: z_def)
  have fin: "finite {x :: real. A k0 * x ^ 2 + B k0 * x + C k0 = 0}" using A_nz[of k0] k0(1)
    by (subst finite_quadratic_equation_solutions_reals) auto
  from X_root[of "g 0"] X_root[of "g 1"] X_root[of "g 2"] g_ge_2 g
    have "(X \<circ> g) ` {0, 1, 2} \<subseteq> {x. A k0 * x ^ 2 + B k0 * x + C k0 = 0}"
    by auto
  hence "card ((X \<circ> g) ` {0, 1, 2}) \<le> card \<dots>"
    by (intro card_mono fin) auto
  also have "\<dots> \<le> 2"
    by (rule card_quadratic_equation_solutions_reals_le_2)
  also have "\<dots> < card {0, 1, 2 :: nat}" by simp
  finally have "\<not>inj_on (X \<circ> g) {0, 1, 2}"
    by (rule pigeonhole)
  then obtain m1 m2 where
    m12: "m1 \<in> {0, 1, 2}" "m2 \<in> {0, 1, 2}" "X (g m1) = X (g m2)" "m1 \<noteq> m2"
    unfolding inj_on_def o_def by blast
  define n and l where "n = min (g m1) (g m2)" and "l = nat \<bar>int (g m1) - g m2\<bar>"
  with m12 g' have l: "l > 0" "X (n + l) = X n"
    by (auto simp: min_def nat_diff_distrib split: if_splits)

  from l have "cfrac_lim (cfrac_drop (n + l) e) = cfrac_lim (cfrac_drop n e)"
    by (simp add: X_def cfrac_remainder_def)
  hence "cfrac_drop (n + l) e = cfrac_drop n e"
    by (simp add: cfrac_lim_eq_iff)
  hence "cfrac_nth (cfrac_drop (n + l) e) = cfrac_nth (cfrac_drop n e)"
    by (simp only:)
  hence period: "cfrac_nth e (n + l + k) = cfrac_nth e (n + k)" for k
    by (simp add: fun_eq_iff add_ac)
  have period: "cfrac_nth e (k + l) = cfrac_nth e k" if "k \<ge> n" for k
    using period[of "k - n"] that by (simp add: add_ac)
  have period: "cfrac_nth e (k + m * l) = cfrac_nth e k" if "k \<ge> n" for k m
    using that
  proof (induction m)
    case (Suc m)
    have "cfrac_nth e (k + Suc m * l) = cfrac_nth e (k + m * l + l)"
      by (simp add: algebra_simps)
    also have "\<dots> = cfrac_nth e (k + m * l)"
      using Suc.prems by (intro period) auto
    also have "\<dots> = cfrac_nth e k"
      using Suc.prems by (intro Suc.IH) auto
    finally show ?case .
  qed simp_all

  from this and l and that[of l n] show ?thesis by (simp add: X_def)
qed

theorem periodic_cfrac_iff_quadratic_irrational:
  assumes "x \<notin> \<rat>" "x \<ge> 0"
  shows   "quadratic_irrational x \<longleftrightarrow> 
             (\<exists>N l. l > 0 \<and> (\<forall>n\<ge>N. cfrac_nth (cfrac_of_real x) (n + l) = cfrac_nth (cfrac_of_real x) n))"
proof safe
  assume *: "quadratic_irrational x"
  with assms have "quadratic_irrational (cfrac_lim (cfrac_of_real x))" by auto
  from quadratic_irrational_imp_periodic_cfrac [OF this] guess N l . note Nl = this
  show "\<exists>N l. l > 0 \<and> (\<forall>n\<ge>N. cfrac_nth (cfrac_of_real x) (n + l) = cfrac_nth (cfrac_of_real x) n)"
    by (rule exI[of _ N], rule exI[of _ l]) (insert Nl(1) Nl(2)[of _ 1], auto)
next
  fix N l assume "l > 0" "\<forall>n\<ge>N. cfrac_nth (cfrac_of_real x) (n + l) = cfrac_nth (cfrac_of_real x) n"
  hence "quadratic_irrational (cfrac_lim (cfrac_of_real x))" using assms
    by (intro periodic_cfrac_imp_quadratic_irrational[of _ l N]) auto
  with assms show "quadratic_irrational x"
    by simp
qed

text \<open>
  The following result can e.g. be used to show that a number is \<^emph>\<open>not\<close> a quadratic
  irrational.
\<close>
lemma quadratic_irrational_cfrac_nth_range_finite:
  assumes "quadratic_irrational (cfrac_lim e)"
  shows   "finite (range (cfrac_nth e))"
proof -
  from quadratic_irrational_imp_periodic_cfrac[OF assms] obtain l N
    where period: "l > 0" "\<And>m n. n \<ge> N \<Longrightarrow> cfrac_nth e (n + m * l) = cfrac_nth e n"
    by metis
  have "cfrac_nth e k \<in> cfrac_nth e ` {..<N+l}" for k
  proof (cases "k < N + l")
    case False
    define n m where "n = N + (k - N) mod l" and "m = (k - N) div l"
    have "cfrac_nth e n \<in> cfrac_nth e ` {..<N+l}"
      using \<open>l > 0\<close> by (intro imageI) (auto simp: n_def)
    also have "cfrac_nth e n = cfrac_nth e (n + m * l)"
      by (subst period) (auto simp: n_def)
    also have "n + m * l = k"
      using False by (simp add: n_def m_def)
    finally show ?thesis .
  qed auto
  hence "range (cfrac_nth e) \<subseteq> cfrac_nth e ` {..<N+l}"
    by blast
  thus ?thesis by (rule finite_subset) auto
qed

end