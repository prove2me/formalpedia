-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.channelFaithfulness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:47:41.380899+00:00
-- url     : https://prove2.me/submissions/dd46c147-fd20-4b6d-a597-b7b95e17e983

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Matrix ComplexConjugate Topology ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P37

/-- Gamma integral in lintegral form. -/
lemma X7M_gamma (m : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * Real.exp (-(r * t))) =
      ENNReal.ofReal (m.factorial / r ^ (m + 1)) := by
  have hI : ∫ t in Ioi (0:ℝ), t ^ m * Real.exp (-(r * t)) = m.factorial / r ^ (m + 1) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m:ℝ) + 1) (by positivity) hr
    rw [show ((m:ℝ) + 1 - 1) = (m:ℝ) by ring, Real.Gamma_nat_eq_factorial] at h
    rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      rw [Real.rpow_natCast])] at h
    rw [h, Real.div_rpow zero_le_one hr.le, Real.one_rpow,
      show ((m:ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have hpos : (0:ℝ) < m.factorial / r ^ (m + 1) := by positivity
  rw [← hI, ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.of_integral_ne_zero (by rw [hI]; exact hpos.ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le

lemma X7M_beta (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (n - 1) / (1 + t) ^ (n + d)) =
      ENNReal.ofReal ((n - 1).factorial * (d - 1).factorial / (n + d - 1).factorial) := by
  set N := n + d - 1 with hN
  have hN1 : N + 1 = n + d := by omega
  have hNf : (0:ℝ) < N.factorial := by positivity
  have step1 : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t ^ (n - 1) / (1 + t) ^ (n + d)) =
      ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (t ^ (n - 1) / N.factorial) *
        ENNReal.ofReal (u ^ N * Real.exp (-((1 + t) * u))) := by
    intro t ht
    have ht' : (0:ℝ) < 1 + t := by linarith [mem_Ioi.mp ht]
    rw [lintegral_const_mul _ (by fun_prop), X7M_gamma N ht', ← ENNReal.ofReal_mul
      (div_nonneg (pow_nonneg (le_of_lt ht) _) hNf.le), hN1]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable
    exact (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ × ℝ =>
      p.1 ^ (n-1) / (N.factorial:ℝ))).mul (ENNReal.measurable_ofReal.comp (by fun_prop :
      Measurable fun p : ℝ × ℝ => p.2 ^ N * Real.exp (-((1 + p.1) * p.2)))))]
  have step2 : ∀ u ∈ Ioi (0:ℝ), (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ (n - 1) / N.factorial) *
        ENNReal.ofReal (u ^ N * Real.exp (-((1 + t) * u)))) =
      ENNReal.ofReal ((n - 1).factorial / N.factorial) *
        ENNReal.ofReal (u ^ (d - 1) * Real.exp (-(1 * u))) := by
    intro u hu
    have hu' : (0:ℝ) < u := hu
    have e : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (t ^ (n - 1) / N.factorial) *
        ENNReal.ofReal (u ^ N * Real.exp (-((1 + t) * u))) =
        ENNReal.ofReal (u ^ N * Real.exp (-u) / N.factorial) *
        ENNReal.ofReal (t ^ (n - 1) * Real.exp (-(u * t))) := by
      intro t ht
      have ht : (0:ℝ) ≤ t := le_of_lt ht
      rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg ht _) hNf.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((1 + t) * u) = -u + -(u * t) by ring, Real.exp_add]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi e]
    rw [lintegral_const_mul _ (by fun_prop), X7M_gamma (n - 1) hu', ← ENNReal.ofReal_mul
      (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : n - 1 + 1 = n := by omega
    rw [this, one_mul]
    have hNn : N = (d - 1) + n := by omega
    rw [hNn, pow_add]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi step2, lintegral_const_mul _ (by fun_prop),
    X7M_gamma (d - 1) one_pos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [one_pow, div_one]
  ring

lemma X7M_expmom (a : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (z ^ a * Real.exp (-(t * z))) ∂(expMeasure 1) =
      ENNReal.ofReal (a.factorial / (1 + t) ^ (a + 1)) := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hg : Measurable fun z : ℝ => ENNReal.ofReal (z ^ a * Real.exp (-(t * z))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hf hg]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  rw [lintegral_congr_ae (g := (Ioi (0:ℝ)).indicator
      (fun z => ENNReal.ofReal (z ^ a * Real.exp (-((1 + t) * z)))))]
  · rw [lintegral_indicator measurableSet_Ioi, X7M_gamma a (by linarith)]
  · filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, gammaPDF_eq]
    rcases lt_or_gt_of_ne hz with h | h
    · rw [indicator_of_notMem (by simpa using h.le), if_neg (by linarith), ENNReal.ofReal_zero,
        zero_mul]
    · rw [indicator_of_mem (by simpa using h), if_pos h.le, ← ENNReal.ofReal_mul (by
        simp [Real.Gamma_one]; positivity)]
      congr 1
      simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, one_mul]
      rw [show -((1 + t) * z) = -z + -(t * z) by ring, Real.exp_add]
      ring

instance X7M_probExp : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

lemma X7M_exp_pos : ∀ᵐ x ∂(expMeasure 1), (0:ℝ) < x := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, ae_withDensity_iff hf]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h

lemma X7M_pi_pos {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ i, (0:ℝ) < z i :=
  eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7M_exp_pos

lemma X7M_pimom {ι : Type*} [Fintype ι] (a : ι → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ z, ENNReal.ofReal (∏ i, (z i ^ a i * Real.exp (-(t * z i))))
      ∂(Measure.pi fun _ : ι => expMeasure 1) =
      ENNReal.ofReal (∏ i, ((a i).factorial / (1 + t) ^ (a i + 1))) := by
  have h1 : ∀ i, ∫ x, x ^ a i * Real.exp (-(t * x)) ∂(expMeasure 1) =
      (a i).factorial / (1 + t) ^ (a i + 1) := by
    intro i
    rw [integral_eq_lintegral_of_nonneg_ae, X7M_expmom (a i) ht, ENNReal.toReal_ofReal
      (by positivity)]
    · filter_upwards [X7M_exp_pos] with x hx
      exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le
    · exact (by fun_prop : Continuous fun x : ℝ => x ^ a i * Real.exp (-(t * x))).aestronglyMeasurable
  have hint : ∀ i, Integrable (fun x : ℝ => x ^ a i * Real.exp (-(t * x))) (expMeasure 1) :=
    fun i => Integrable.of_integral_ne_zero (by rw [h1]; positivity)
  have h2 := integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun (i : ι) (x : ℝ) => x ^ a i * Real.exp (-(t * x)))
    (μ := fun _ : ι => expMeasure 1)
  simp only [h1] at h2
  rw [← h2, ofReal_integral_eq_lintegral_ofReal]
  · exact Integrable.fintype_prod (f := fun (i : ι) (x : ℝ) => x ^ a i * Real.exp (-(t * x))) hint
  · filter_upwards [X7M_pi_pos] with z hz
    exact Finset.prod_nonneg fun i _ => mul_nonneg (pow_nonneg (hz i).le _) (Real.exp_pos _).le

lemma X7M_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

/-- Reduction of a simplex-law integral of a monomial to the exponential product. -/
lemma X7M_reduce {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℕ) :
    (∫ p, ∏ i, p i ^ a i ∂simplexLaw ι) =
      ∫ z, (∏ i, z i ^ a i) / (∑ i, z i) ^ (∑ i, a i) ∂(Measure.pi fun _ : ι => expMeasure 1) := by
  rw [simplexLaw, integral_map X7M_norm_meas.aemeasurable
    (by fun_prop : Continuous fun p : ι → ℝ => ∏ i, p i ^ a i).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [X7M_pi_pos] with z hz
  have hS : (∑ i, z i) ≠ 0 := (Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty).ne'
  simp only [normalizePopulation, hS, if_false, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum]

lemma X7M_main {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℕ) :
    (∫ p, ∏ i, p i ^ a i ∂simplexLaw ι) =
      ((Fintype.card ι - 1).factorial * ∏ i, ((a i).factorial : ℝ)) /
        (Fintype.card ι + ∑ i, a i - 1).factorial := by
  set d := Fintype.card ι with hd
  have hd1 : 1 ≤ d := Fintype.card_pos
  set n := ∑ i, a i with hn
  rw [X7M_reduce]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have ha : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)
    simp [ha, h0]
    rw [div_self (by positivity)]
  · set π := Measure.pi fun _ : ι => expMeasure 1
    have hnf : (0:ℝ) < (n - 1).factorial := by positivity
    -- pointwise Gamma representation
    have hrep : ∀ᵐ z ∂π, ENNReal.ofReal ((∏ i, z i ^ a i) / (∑ i, z i) ^ n) =
        ENNReal.ofReal (1 / (n - 1).factorial) * ∫⁻ t in Ioi (0:ℝ),
          ENNReal.ofReal ((∏ i, (z i ^ a i * Real.exp (-(t * z i)))) * t ^ (n - 1)) := by
      filter_upwards [X7M_pi_pos] with z hz
      have hS : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
      have hF : 0 ≤ ∏ i, z i ^ a i := Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _
      have e : ∀ t, (∏ i, (z i ^ a i * Real.exp (-(t * z i)))) * t ^ (n - 1) =
          (∏ i, z i ^ a i) * (t ^ (n - 1) * Real.exp (-((∑ i, z i) * t))) := by
        intro t
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_mul]
        simp only [neg_mul, Finset.sum_neg_distrib, mul_comm t]
        ring
      simp_rw [e]
      have hm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (n - 1) * Real.exp (-((∑ i, z i) * t))) :=
        ENNReal.measurable_ofReal.comp (by fun_prop)
      simp_rw [ENNReal.ofReal_mul hF]
      rw [lintegral_const_mul _ hm, X7M_gamma (n - 1) hS, Nat.sub_add_cancel hpos,
        ← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hinner : ∀ t ∈ Ioi (0:ℝ), (∫⁻ z, ENNReal.ofReal
          ((∏ i, (z i ^ a i * Real.exp (-(t * z i)))) * t ^ (n - 1)) ∂π) =
        ENNReal.ofReal (∏ i, ((a i).factorial : ℝ)) *
          ENNReal.ofReal (t ^ (n - 1) / (1 + t) ^ (n + d)) := by
      intro t ht
      have ht0 : (0:ℝ) ≤ t := le_of_lt ht
      simp_rw [ENNReal.ofReal_mul' (pow_nonneg ht0 (n - 1))]
      have hm1 : Measurable fun z : ι → ℝ =>
          ENNReal.ofReal (∏ i, (z i ^ a i * Real.exp (-(t * z i)))) :=
        ENNReal.measurable_ofReal.comp (by fun_prop)
      rw [lintegral_mul_const _ hm1, X7M_pimom a ht0, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← hn, ← hd]
      ring
    have hmeas : Measurable (Function.uncurry fun (z : ι → ℝ) (t : ℝ) =>
        ENNReal.ofReal ((∏ i, (z i ^ a i * Real.exp (-(t * z i)))) * t ^ (n - 1))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have hL : (∫⁻ z, ENNReal.ofReal ((∏ i, z i ^ a i) / (∑ i, z i) ^ n) ∂π) =
        ENNReal.ofReal ((n - 1).factorial * (d - 1).factorial / (n + d - 1).factorial
          / (n - 1).factorial * ∏ i, ((a i).factorial : ℝ)) := by
      rw [lintegral_congr_ae hrep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_lintegral_swap hmeas.aemeasurable,
        setLIntegral_congr_fun measurableSet_Ioi hinner,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        X7M_beta n d hpos hd1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [integral_eq_lintegral_of_nonneg_ae, hL, ENNReal.toReal_ofReal (by positivity)]
    · rw [add_comm d n]
      field_simp
    · filter_upwards [X7M_pi_pos] with z hz
      exact div_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hz i).le _)
        (pow_nonneg (Finset.sum_nonneg fun i _ => (hz i).le) _)
    · exact (by fun_prop : Measurable fun z : ι → ℝ =>
        (∏ i, z i ^ a i) / (∑ i, z i) ^ n).aestronglyMeasurable

lemma X7M_gen {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (a : ι → ℕ) (s : Finset ι)
    (ha : ∀ k ∉ s, a k = 0) (f : (ι → ℝ) → ℝ) (hf : ∀ p, ∏ k ∈ s, p k ^ a k = f p) :
    (∫ p, f p ∂simplexLaw ι) =
      ((Fintype.card ι - 1).factorial * ∏ k ∈ s, ((a k).factorial : ℝ)) /
        (Fintype.card ι + ∑ k ∈ s, a k - 1).factorial := by
  have h1 : ∀ p : ι → ℝ, ∏ k, p k ^ a k = f p := by
    intro p
    rw [← hf, Finset.prod_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk, pow_zero]
  have h2 : ∏ k, ((a k).factorial : ℝ) = ∏ k ∈ s, ((a k).factorial : ℝ) := by
    rw [Finset.prod_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk]; simp
  have h3 : ∑ k, a k = ∑ k ∈ s, a k := by
    rw [Finset.sum_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk]
  simp_rw [← h1]
  rw [X7M_main a, h2, h3]

lemma X7M_first {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i : ι) :
    (∫ p, p i ∂simplexLaw ι) = 1 / (Fintype.card ι : ℝ) := by
  rw [X7M_gen (fun k => if k = i then 1 else 0) {i} (by intro k hk; simp at hk; simp [hk])
    (fun p => p i) (by intro p; simp)]
  obtain ⟨e, he⟩ : ∃ e, Fintype.card ι = e + 1 := ⟨Fintype.card ι - 1, by
    have := Fintype.card_pos (α := ι); omega⟩
  simp only [he, Finset.prod_singleton, Finset.sum_singleton, if_true]
  rw [show e + 1 + 1 - 1 = e + 1 by omega, show e + 1 - 1 = e by omega, Nat.factorial_succ]
  have : (0:ℝ) < e.factorial := by positivity
  push_cast
  field_simp
  simp
  rw [Nat.factorial_succ]; push_cast; ring

lemma X7M_second {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i j : ι) :
    (∫ p, p i * p j ∂simplexLaw ι) = (1 + if i = j then 1 else 0) /
      ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  obtain ⟨e, he⟩ : ∃ e, Fintype.card ι = e + 1 := ⟨Fintype.card ι - 1, by
    have := Fintype.card_pos (α := ι); omega⟩
  have : (0:ℝ) < e.factorial := by positivity
  by_cases hij : i = j
  · subst hij
    rw [X7M_gen (fun k => if k = i then 2 else 0) {i} (by intro k hk; simp at hk; simp [hk])
      (fun p => p i * p i) (by intro p; simp [sq])]
    simp only [he, Finset.prod_singleton, Finset.sum_singleton, if_true]
    rw [show e + 1 + 2 - 1 = e + 2 by omega, show e + 1 - 1 = e by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    norm_num [Nat.factorial]
    ring
  · rw [X7M_gen (fun k => if k = i then 1 else if k = j then 1 else 0) {i, j}
      (by intro k hk; simp at hk; simp [hk.1, hk.2]) (fun p => p i * p j)
      (by intro p; simp [hij, Ne.symm hij])]
    simp only [he, Finset.prod_pair hij, Finset.sum_pair hij, if_true, if_neg (Ne.symm hij),
      if_neg hij]
    rw [show e + 1 + (1 + 1) - 1 = e + 2 by omega, show e + 1 - 1 = e by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    norm_num
    rw [Nat.factorial_succ]
    push_cast
    ring

lemma X7U_frob_sq {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    frobNorm X ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  unfold frobNorm
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp [Complex.sq_norm]

lemma X7U_normSq_re (z : ℂ) : Complex.normSq z = (conj z * z).re := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma X7U_kraus_lin {ι K α : Type*} [Fintype ι] [Fintype K] [Fintype α]
    (A : K → Matrix ι ι ℂ) (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    krausApply A (∑ a, f a • X a) = ∑ a, f a • krausApply A (X a) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma X7U_diag_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℂ) :
    Matrix.diagonal p = ∑ i, p i • Matrix.single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : a = b
  · subst h; simp [Finset.sum_ite_eq']
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    aesop

lemma X7U_offDiag_sum {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : α → ℂ) (X : α → Matrix ι ι ℂ) :
    offDiagonal (∑ a, f a • X a) = ∑ a, f a • offDiagonal (X a) := by
  ext l m
  simp only [offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

lemma X7U_E_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (q : ι → ℂ) :
    offDiagonal (E (Matrix.diagonal q)) = ∑ i, q i • channelOutput E i := by
  obtain ⟨m, A, -, hA⟩ := hE
  rw [hA, X7U_diag_eq, X7U_kraus_lin, X7U_offDiag_sum]
  simp [channelOutput, hA]

lemma X7U_kraus_single {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    (A : K → Matrix ι ι ℂ) (i l m : ι) :
    krausApply A (Matrix.single i i 1) l m = ∑ k, A k l i * conj (A k m i) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i] <;> simp +contextual [eq_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma X7U_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (i l m : ι) : conj (channelOutput E i l m) = channelOutput E i m l := by
  obtain ⟨n, A, -, hA⟩ := hE
  simp only [channelOutput, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.diag,
    hA, X7U_kraus_single]
  by_cases h : l = m
  · subst h; simp
  · simp [h, Ne.symm h, map_sum, mul_comm]

lemma X7U_resp {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (i j : ι) : channelResponse E i j =
      ∑ l, ∑ m, (conj (channelOutput E i l m) * channelOutput E j l m).re := by
  simp only [channelResponse, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum,
    X7U_herm E hE]
  rw [Finset.sum_comm]

lemma X7U_normSq_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) (z : ι → ℂ) :
    Complex.normSq (∑ i, (x i : ℂ) * z i) = ∑ i, ∑ j, x i * x j * (conj (z i) * z j).re := by
  rw [X7U_normSq_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  rw [show (x i : ℂ) * conj (z i) * ((x j : ℂ) * z j) =
    ((x i * x j : ℝ) : ℂ) * (conj (z i) * z j) by push_cast; ring, Complex.re_ofReal_mul]

lemma X7U_swap3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

lemma X7U_key {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (x : ι → ℝ) : quadratic (channelResponse E) x =
      ∑ l, ∑ m, Complex.normSq (∑ i, (x i : ℂ) * channelOutput E i l m) := by
  simp only [quadratic, X7U_resp E hE, X7U_normSq_sum, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => X7U_swap3 _).trans ?_
  refine (X7U_swap3 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


lemma X7I_gen {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (p : ι → ℝ) : generated E p = quadratic (channelResponse E) p := by
  rw [X7U_key E hE]
  have h := X7U_E_diag E hE (fun i => (p i : ℂ))
  have hc : generated E p = ∑ l, ∑ m, Complex.normSq
      (offDiagonal (E (inputDensity p)) l m) := by
    simp only [generated, coherence, offDiagonal, Matrix.sub_apply, Matrix.diagonal_apply,
      Matrix.diag]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  rw [hc, inputDensity, h]
  simp [Matrix.sum_apply]

lemma X7I_Gii {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E)
    (i : ι) : channelResponse E i i = ∑ l, ∑ m, Complex.normSq (channelOutput E i l m) := by
  rw [X7U_resp E hE]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [X7U_normSq_re]

lemma X7I_sumG {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι) (hE : IsChannel E) :
    0 ≤ ∑ i, ∑ j, channelResponse E i j := by
  have h := X7U_key E hE (fun _ => 1)
  simp only [quadratic, one_mul, mul_one] at h
  rw [h]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma X7I_int2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i j : ι) :
    Integrable (fun p : ι → ℝ => p i * p j) (simplexLaw ι) :=
  Integrable.of_integral_ne_zero (by
    rw [X7M_second]
    have : (0:ℝ) < Fintype.card ι := by simp [Fintype.card_pos]
    positivity)

lemma X7I_intQ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) :
    Integrable (fun p => quadratic G p) (simplexLaw ι) := by
  have : (fun p => quadratic G p) = fun p : ι → ℝ => ∑ i, ∑ j, G i j * (p i * p j) := by
    funext p; simp only [quadratic]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (X7I_int2 i j).const_mul _

lemma X7I_intQ_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ) :
    (∫ p, quadratic G p ∂simplexLaw ι) = (∑ i, ∑ j, G i j + G.trace) /
      ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  have : (fun p => quadratic G p) = fun p : ι → ℝ => ∑ i, ∑ j, G i j * (p i * p j) := by
    funext p; simp only [quadratic]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j, Integrable (fun p : ι → ℝ => G i j * (p i * p j)) (simplexLaw ι) :=
    fun i j => (X7I_int2 i j).const_mul _
  rw [this, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have h2 : ∀ i, ∫ p, (∑ j, G i j * (p i * p j)) ∂simplexLaw ι =
      ∑ j, G i j * ((1 + if i = j then 1 else 0) /
        ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))) := fun i => by
    rw [integral_finsetSum _ fun j _ => hint i j]
    simp only [integral_const_mul, X7M_second]
  simp only [h2, mul_div_assoc', ← Finset.sum_div, mul_add, mul_one, mul_ite, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace,
    Matrix.diag]

lemma X7I_cgp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) : cgp E = (∑ i, ∑ j, channelResponse E i j + (channelResponse E).trace) /
      ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  rw [← X7I_intQ_eq]
  simp only [cgp, moment, pow_one, X7I_gen E hE]

lemma X7I_cgp_zero {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) : cgp E = 0 ↔ ∀ i, channelOutput E i = 0 := by
  have hd : (0:ℝ) < Fintype.card ι := by simp [Fintype.card_pos]
  have hGii : ∀ i, 0 ≤ channelResponse E i i := fun i => by
    rw [X7I_Gii E hE]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hT : 0 ≤ (channelResponse E).trace := Finset.sum_nonneg fun i _ => hGii i
  have hS := X7I_sumG E hE
  rw [X7I_cgp E hE]
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    have hT0 : (channelResponse E).trace = 0 := by
      rcases h with h | h
      · linarith
      · exfalso; have : (0:ℝ) < (Fintype.card ι : ℝ) * (Fintype.card ι + 1) := by positivity
        linarith
    intro i
    have hi : channelResponse E i i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hGii i).mp hT0 i (Finset.mem_univ _)
    rw [X7I_Gii E hE] at hi
    ext l m
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).mp hi l (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).mp h1 m
      (Finset.mem_univ _)
    simpa using h2
  · intro h
    have hG : ∀ i j, channelResponse E i j = 0 := fun i j => by
      simp [channelResponse, h]
    simp [hG, Matrix.trace]

lemma X7I_gen_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι)
    (hE : IsChannel E) (h : ∀ i, channelOutput E i = 0) (p : ι → ℝ) : generated E p = 0 := by
  rw [X7I_gen E hE]
  have hG : ∀ i j, channelResponse E i j = 0 := fun i j => by
    simp [channelResponse, h]
  simp [quadratic, hG]

lemma X7I_both_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Superop ι ι)
    (hE : IsChannel E) (h : ∀ i, channelOutput E i = 0) : cgp E = 0 ∧ cgpd E = 0 := by
  have hc : cgp E = 0 := by
    simp [cgp, moment, X7I_gen_zero E hE h]
  refine ⟨hc, ?_⟩
  simp [cgpd, coherenceVariance, hc, X7I_gen_zero E hE h]

lemma X7I_single_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Matrix.diagonal (Matrix.diag (Matrix.single i i (1 : ℂ))) = Matrix.single i i 1 := by
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.diag, Matrix.single_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h]; intro h1 h2; exact absurd (h1.symm.trans h2) h

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : Superop ι ι)
    (hE : IsChannel E) (_hu : E 1 = 1) :
    (cgp E = 0 ∧ cgpd E = 0) ↔ ∀ M : Matrix ι ι ℂ, offDiagonal (E (Matrix.diagonal (Matrix.diag M))) = 0 := by
  constructor
  · rintro ⟨h, -⟩ M
    have h0 := (X7I_cgp_zero E hE).mp h
    rw [X7U_E_diag E hE]
    simp [h0]
  · intro h
    apply X7I_both_zero E hE
    intro i
    have := h (Matrix.single i i 1)
    rwa [X7I_single_diag] at this
