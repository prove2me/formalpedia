-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.localizedDistributed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:31:14.930772+00:00
-- url     : https://prove2.me/submissions/f7fbe07f-0ca4-496f-a788-36e7bcfda5a6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Matrix ComplexConjugate Topology ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P37

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

/-- count-weight of a 4-tuple -/
def X7Q_w {ι : Type*} [DecidableEq ι] (i j k l : ι) : ℝ :=
  1 + (if i = j then 1 else 0) + (if i = k then 1 else 0) + (if i = l then 1 else 0) +
    (if j = k then 1 else 0) + (if j = l then 1 else 0) + (if k = l then 1 else 0) +
    (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
    (if i = l ∧ j = k then 1 else 0) +
    2 * ((if i = j ∧ j = k then 1 else 0) + (if i = j ∧ j = l then 1 else 0) +
      (if i = k ∧ k = l then 1 else 0) + (if j = k ∧ k = l then 1 else 0)) +
    6 * (if i = j ∧ j = k ∧ k = l then 1 else 0)

lemma X7Q_fact {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    ∏ m, (((if m = i then 1 else 0) + (if m = j then 1 else 0) + (if m = k then 1 else 0) +
      (if m = l then 1 else 0) : ℕ).factorial : ℝ) = X7Q_w i j k l := by
  rw [← Finset.prod_subset (Finset.subset_univ {i, j, k, l})]
  · by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
      subst_vars <;> simp_all [X7Q_w, Finset.prod_insert, Eq.comm] <;> norm_num [Nat.factorial]
  · intro m _ hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2]

lemma X7Q_m4 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i j k l : ι) :
    (∫ p, p i * p j * p k * p l ∂simplexLaw ι) = X7Q_w i j k l / fourthDenominator (Fintype.card ι) := by
  set a : ι → ℕ := fun m => (if m = i then 1 else 0) + (if m = j then 1 else 0) +
    (if m = k then 1 else 0) + (if m = l then 1 else 0) with ha
  have hmono : ∀ p : ι → ℝ, ∏ m, p m ^ a m = p i * p j * p k * p l := by
    intro p
    simp only [ha, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
      Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∑ m, a m = 4 := by
    simp only [ha, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [← hmono]
  rw [X7M_main a, hsum, X7Q_fact]
  obtain ⟨e, he⟩ : ∃ e, Fintype.card ι = e + 1 := ⟨Fintype.card ι - 1, by
    have := Fintype.card_pos (α := ι); omega⟩
  rw [he, show e + 1 + 4 - 1 = e + 4 by omega, show e + 1 - 1 = e by omega]
  simp only [fourthDenominator, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  have : (0:ℝ) < e.factorial := by positivity
  field_simp
  ring

lemma X7Q_contract {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ)
    (hs : G.IsSymm) (hz : G.mulVec (fun _ => 1) = 0) :
    ∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l * X7Q_w i j k l =
      G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G := by
  have hsym : ∀ i j, G j i = G i j := fun i j => hs.apply i j
  have hr : ∀ i, ∑ j, G i j = 0 := fun i => by
    have := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply] at this
    exact this
  have hc : ∀ j, ∑ i, G i j = 0 := fun j => by
    exact (Finset.sum_congr rfl fun i _ => hsym j i).trans (hr j)
  simp only [X7Q_w, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.mul_sum,
    Finset.sum_ite_irrel,
    ← Finset.sum_mul, hr, hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  have h0 : ∑ i, ∑ j, G i j * G j j = 0 := by
    rw [Finset.sum_comm]; simp [← Finset.sum_mul, hc]
  rw [h0]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, diagonalSq, hsym, sq]
  ring

lemma X7Q_w_pos {ι : Type*} [DecidableEq ι] (i j k l : ι) : 0 < X7Q_w i j k l := by
  unfold X7Q_w; positivity

lemma X7Q_main {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ)
    (hs : G.IsSymm) (hz : G.mulVec (fun _ => 1) = 0) :
    (∫ p, (quadratic G p) ^ 2 ∂simplexLaw ι) =
      (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) / fourthDenominator (Fintype.card ι) := by
  have hexp : ∀ p : ι → ℝ, (quadratic G p) ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, G i j * G k l * (p i * p j * p k * p l) := by
    intro p
    simp only [quadratic, sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hint : ∀ i j k l, Integrable (fun p : ι → ℝ => G i j * G k l * (p i * p j * p k * p l))
      (simplexLaw ι) := fun i j k l =>
    (Integrable.of_integral_ne_zero (by
      rw [X7Q_m4]
      have := X7Q_w_pos i j k l
      have : (0:ℝ) < fourthDenominator (Fintype.card ι) := by
        unfold fourthDenominator; have := Fintype.card_pos (α := ι); positivity
      positivity)).const_mul _
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l]
  have h2 : ∀ i, ∫ p, (∑ j, ∑ k, ∑ l, G i j * G k l * (p i * p j * p k * p l)) ∂simplexLaw ι =
      ∑ j, ∫ p, (∑ k, ∑ l, G i j * G k l * (p i * p j * p k * p l)) ∂simplexLaw ι := fun i =>
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => hint i j k l
  have h3 : ∀ i j, ∫ p, (∑ k, ∑ l, G i j * G k l * (p i * p j * p k * p l)) ∂simplexLaw ι =
      ∑ k, ∫ p, (∑ l, G i j * G k l * (p i * p j * p k * p l)) ∂simplexLaw ι := fun i j =>
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint i j k l
  have h4 : ∀ i j k, ∫ p, (∑ l, G i j * G k l * (p i * p j * p k * p l)) ∂simplexLaw ι =
      ∑ l, ∫ p, G i j * G k l * (p i * p j * p k * p l) ∂simplexLaw ι := fun i j k =>
    integral_finsetSum _ fun l _ => hint i j k l
  simp only [h2, h3, h4, integral_const_mul, X7Q_m4, mul_div_assoc', ← Finset.sum_div]
  rw [X7Q_contract G hs hz]

lemma X7G_row {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (i : ι) : ∑ j, transition U i j = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def,
    Complex.mul_conj] at h
  simp only [transition]
  exact_mod_cast h

lemma X7G_col {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (j : ι) : ∑ i, transition U i j = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def,
    mul_comm (conj _), Complex.mul_conj] at h
  simp only [transition]
  exact_mod_cast h

lemma X7G_frob {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    ∑ l, ∑ m, Complex.normSq (X l m) = ((Xᴴ * X).trace).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

lemma X7G_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (p : ι → ℝ)
    (l m : ι) : conjSuperop U (inputDensity p) l m = ∑ k, U l k * (p k : ℂ) * conj (U m k) := by
  simp only [conjSuperop, inputDensity, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]

lemma X7G_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (p : ι → ℝ)
    (i : ι) : conjSuperop U (inputDensity p) i i = (((transition U).mulVec p i : ℝ) : ℂ) := by
  rw [X7G_entry]
  simp only [Matrix.mulVec, dotProduct, transition, Complex.ofReal_sum, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_right_comm, Complex.mul_conj]

lemma X7G_offsum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (l : ι) :
    (∑ m, if l = m then 0 else f m) = ∑ m, f m - f l := by
  rw [show (∑ m, if l = m then 0 else f m) = ∑ m, (f m - if l = m then f m else 0) from
    Finset.sum_congr rfl fun m _ => by split_ifs <;> simp]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

lemma X7G_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic G x = x ⬝ᵥ G.mulVec x := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

lemma X7G_form {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (x : ι → ℝ) :
    x ⬝ᵥ (response U).mulVec x = x ⬝ᵥ x - (transition U).mulVec x ⬝ᵥ (transition U).mulVec x := by
  rw [response, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma X7J_genquad {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) :
    generated (conjSuperop U) p = quadratic (response U) p := by
  set P := transition U
  have hfull : ∑ l, ∑ m, Complex.normSq (conjSuperop U (inputDensity p) l m) = ∑ k, p k ^ 2 := by
    rw [X7G_frob]
    have hUU : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU
    have : (conjSuperop U (inputDensity p))ᴴ * conjSuperop U (inputDensity p) =
        U * ((inputDensity p)ᴴ * inputDensity p) * Uᴴ := by
      simp only [conjSuperop, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
    simp [inputDensity, Matrix.trace, Matrix.diagonal_conjTranspose, Complex.re_sum, sq]
  have hdiag : ∀ l, Complex.normSq (conjSuperop U (inputDensity p) l l) = (P.mulVec p l) ^ 2 := by
    intro l; rw [X7G_diag, Complex.normSq_ofReal, sq]
  have hcoh : generated (conjSuperop U) p = ∑ l, ∑ m,
      Complex.normSq (conjSuperop U (inputDensity p) l m) -
      ∑ l, Complex.normSq (conjSuperop U (inputDensity p) l l) := by
    simp only [generated, coherence]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact X7G_offsum _ l
  rw [hcoh, hfull, X7G_quad, X7G_form]
  simp only [hdiag, dotProduct, sq]
  rfl

lemma X7J_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (i : ι) : ∑ j, response U i j = 0 := by
  simp only [response, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, X7G_row U hU, mul_one, X7G_col U hU, sub_self]

lemma X7J_int2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (i j : ι) :
    Integrable (fun p : ι → ℝ => p i * p j) (simplexLaw ι) :=
  Integrable.of_integral_ne_zero (by rw [X7M_second]; positivity)

lemma X7J_cgp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    cgp (conjSuperop U) = (response U).trace /
      ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
  have h1 : cgp (conjSuperop U) = ∑ i, ∑ j, response U i j * ∫ p, p i * p j ∂simplexLaw ι := by
    have e : (fun p => generated (conjSuperop U) p ^ 1) =
        fun p : ι → ℝ => ∑ i, ∑ j, response U i j * (p i * p j) := by
      funext p
      rw [pow_one, X7J_genquad U hU, quadratic]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [cgp, moment]
    rw [e, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (X7J_int2 i j).const_mul (response U i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (X7J_int2 i j).const_mul (response U i j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [h1]
  simp_rw [X7M_second]
  have hi : ∀ i, ∑ j, response U i j * ((1 + if i = j then (1:ℝ) else 0) /
      ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))) =
      response U i i / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
    intro i
    have : ∀ j, response U i j * ((1 + if i = j then (1:ℝ) else 0) /
        ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))) =
        (response U i j + if i = j then response U i j else 0) /
        ((Fintype.card ι : ℝ) * (Fintype.card ι + 1)) := by
      intro j; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_div, Finset.sum_add_distrib,
      X7J_rowsum U hU, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_div]
  rfl


instance X7J_prob {ι : Type*} [Fintype ι] : IsProbabilityMeasure (simplexLaw ι) := by
  unfold simplexLaw
  exact Measure.isProbabilityMeasure_map X7M_norm_meas.aemeasurable

/-- a.e. the simplex law lives in the unit cube. -/
lemma X7J_ae_cube {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᵐ p ∂simplexLaw ι, p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
  unfold simplexLaw
  refine (ae_map_iff (p := fun p => p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1))
    X7M_norm_meas.aemeasurable
    (isCompact_univ_pi (fun _ => isCompact_Icc)).isClosed.measurableSet).2 ?_
  filter_upwards [X7M_pi_pos] with z hz
  have hS : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  simp only [normalizePopulation, hS.ne', if_false]
  intro i _
  refine ⟨div_nonneg (hz i).le hS.le, (div_le_one hS).2 ?_⟩
  exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)

lemma X7J_cont {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Continuous (generated (conjSuperop U)) := by
  unfold generated coherence conjSuperop inputDensity
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · refine Complex.continuous_normSq.comp ?_
    simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    fun_prop

lemma X7J_bdd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) :
    ∃ C, ∀ᵐ p ∂simplexLaw ι, |generated (conjSuperop U) p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0:ℝ)) (b := 1))).exists_bound_of_continuousOn
    (X7J_cont U).continuousOn
  refine ⟨C, ?_⟩
  filter_upwards [X7J_ae_cube] with p hp
  exact hC p hp

lemma X7J_int {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (t : ℝ) :
    Integrable (fun p => Real.exp (t * generated (conjSuperop U) p)) (simplexLaw ι) := by
  obtain ⟨C, hC⟩ := X7J_bdd U
  refine Integrable.of_bound (C := Real.exp (|t| * C)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul (X7J_cont U))).aestronglyMeasurable
  · filter_upwards [hC] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc t * generated (conjSuperop U) p ≤ |t * generated (conjSuperop U) p| := le_abs_self _
      _ = |t| * |generated (conjSuperop U) p| := abs_mul _ _
      _ ≤ |t| * C := mul_le_mul_of_nonneg_left hp (abs_nonneg _)


lemma X7J_intpow {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (k : ℕ) :
    Integrable (fun p => generated (conjSuperop U) p ^ k) (simplexLaw ι) := by
  obtain ⟨C, hC⟩ := X7J_bdd U
  refine Integrable.of_bound (C := |C| ^ k) ?_ ?_
  · exact ((X7J_cont U).pow k).aestronglyMeasurable
  · filter_upwards [hC] with p hp
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hp.trans (le_abs_self C)) k

lemma X7J_var {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) :
    cgpd (conjSuperop U) ^ 2 = moment (conjSuperop U) 2 - cgp (conjSuperop U) ^ 2 := by
  rw [cgpd, coherenceVariance, Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)]
  set X := generated (conjSuperop U)
  set c := cgp (conjSuperop U)
  have e : (fun p => (X p - c) ^ 2) = fun p => (X p ^ 2 - (2 * c) * X p ^ 1) + c ^ 2 := by
    funext p; ring
  rw [e, integral_add (f := fun p => X p ^ 2 - 2 * c * X p ^ 1) (g := fun _ => c ^ 2)
    ((X7J_intpow U 2).sub ((X7J_intpow U 1).const_mul _)) (integrable_const _),
    integral_sub (f := fun p => X p ^ 2) (g := fun p => 2 * c * X p ^ 1)
    (X7J_intpow U 2) ((X7J_intpow U 1).const_mul _), integral_const_mul,
    integral_const]
  have h1 : ∫ p, X p ^ 1 ∂simplexLaw ι = c := rfl
  have h2 : ∫ p, X p ^ 2 ∂simplexLaw ι = moment (conjSuperop U) 2 := rfl
  rw [h1, h2]
  simp
  ring

lemma X7J_symm {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    (response U).IsSymm := by
  simp [Matrix.IsSymm, response, Matrix.transpose_sub, Matrix.transpose_mul]

lemma X7J_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : (response U).mulVec (fun _ => 1) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply]
  exact X7J_rowsum U hU i

lemma X7J_mom2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    moment (conjSuperop U) 2 = ((response U).trace ^ 2 + 2 * (response U * response U).trace +
      6 * diagonalSq (response U)) / fourthDenominator (Fintype.card ι) := by
  rw [← X7Q_main _ (X7J_symm U) (X7J_mulVec U hU)]
  simp only [moment]
  simp_rw [X7J_genquad U hU]

lemma X7J_cgpd2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    cgpd (conjSuperop U) ^ 2 = ((response U).trace ^ 2 + 2 * (response U * response U).trace +
      6 * diagonalSq (response U)) / fourthDenominator (Fintype.card ι) -
      ((response U).trace / ((Fintype.card ι : ℝ) * (Fintype.card ι + 1))) ^ 2 := by
  rw [X7J_var, X7J_mom2 U hU, X7J_cgp U hU]

def X7L_blk (c s c' s' : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(c:ℂ), -(s:ℂ), 0, 0; (s:ℂ), (c:ℂ), 0, 0; 0, 0, (c':ℂ), -(s':ℂ); 0, 0, (s':ℂ), (c':ℂ)]

lemma X7L_loc : localized = X7L_blk (Real.cos (Real.pi / 4)) (Real.sin (Real.pi / 4)) 1 0 := by
  have e : 2 * (Real.pi / 4) / 2 = Real.pi / 4 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localized, blockPair, rotY, X7L_blk, e]

lemma X7L_dis : distributed = X7L_blk (Real.cos (Real.pi / 8)) (Real.sin (Real.pi / 8))
    (Real.cos (Real.pi / 8)) (Real.sin (Real.pi / 8)) := by
  have e : 2 * (Real.pi / 8) / 2 = Real.pi / 8 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [distributed, blockPair, rotY, X7L_blk, e]

lemma X7L_unit (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1) :
    X7L_blk c s c' s' ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hc : ((c:ℂ)) ^ 2 + (s:ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hc' : ((c':ℂ)) ^ 2 + (s':ℂ) ^ 2 = 1 := by exact_mod_cast h'
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7L_blk, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply, Matrix.one_apply] <;>
    first | exact hc | exact hc' | ring1 | linear_combination hc | linear_combination hc'

lemma X7L_trans (c s c' s' : ℝ) :
    transition (X7L_blk c s c' s') = !![c^2, s^2, 0, 0; s^2, c^2, 0, 0; 0, 0, c'^2, s'^2; 0, 0, s'^2, c'^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transition, X7L_blk, Complex.normSq_apply, sq]

def X7L_G (k k' : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![k, -k, 0, 0; -k, k, 0, 0; 0, 0, k', -k'; 0, 0, -k', k']

lemma X7L_resp (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1) :
    response (X7L_blk c s c' s') = X7L_G (2 * c^2 * s^2) (2 * c'^2 * s'^2) := by
  have hs : s ^ 2 = 1 - c ^ 2 := by linarith
  have hs' : s' ^ 2 = 1 - c' ^ 2 := by linarith
  rw [response, X7L_trans]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7L_G, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    (try simp only [hs, hs']) <;> ring

lemma X7L_gen (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1) (p : Fin 4 → ℝ) :
    generated (conjSuperop (X7L_blk c s c' s')) p =
      2 * c^2 * s^2 * (p 0 - p 1) ^ 2 + 2 * c'^2 * s'^2 * (p 2 - p 3) ^ 2 := by
  rw [X7J_genquad _ (X7L_unit c s c' s' h h') p, X7L_resp c s c' s' h h']
  simp [quadratic, X7L_G, Fin.sum_univ_four]
  ring

lemma X7L_tr (k k' : ℝ) : (X7L_G k k').trace = 2 * k + 2 * k' := by
  simp [X7L_G, Matrix.trace, Fin.sum_univ_four]; ring

lemma X7L_tr2 (k k' : ℝ) : (X7L_G k k' * X7L_G k k').trace = 4 * k ^ 2 + 4 * k' ^ 2 := by
  simp [X7L_G, Matrix.trace, Fin.sum_univ_four, Matrix.mul_apply]; ring

lemma X7L_dsq (k k' : ℝ) : diagonalSq (X7L_G k k') = 2 * k ^ 2 + 2 * k' ^ 2 := by
  simp [X7L_G, diagonalSq, Fin.sum_univ_four]; ring

lemma X7L_c4 : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma X7L_s4 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
  rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma X7L_cs8 : 2 * Real.cos (Real.pi / 8) ^ 2 * Real.sin (Real.pi / 8) ^ 2 = 1 / 4 := by
  have h := Real.sin_two_mul (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring] at h
  have : (2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8)) ^ 2 = 1 / 2 := by rw [← h, X7L_s4]
  nlinarith

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution :
    localized ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧ distributed ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    cgp (conjSuperop localized) = 1 / 20 ∧ cgp (conjSuperop distributed) = 1 / 20 ∧
    cgpd (conjSuperop localized) ^ 2 = 13 / 2800 ∧ cgpd (conjSuperop distributed) ^ 2 = 1 / 600 ∧
    Papers.Independent.Information100.P37.moment (conjSuperop localized) 2 = 1 / 140 ∧
    Papers.Independent.Information100.P37.moment (conjSuperop distributed) 2 = 1 / 240 ∧
    response localized = (1 / 2 : ℝ) • !![1,-1,0,0; -1,1,0,0; 0,0,0,0; 0,0,0,0] ∧
    response distributed = (1 / 4 : ℝ) • !![1,-1,0,0; -1,1,0,0; 0,0,1,-1; 0,0,-1,1] ∧
    ((response localized).trace, (response localized * response localized).trace,
      diagonalSq (response localized)) = (1, 1, 1 / 2) ∧
    ((response distributed).trace, (response distributed * response distributed).trace,
      diagonalSq (response distributed)) = (1, 1 / 2, 1 / 4) ∧
    (∀ p : Fin 4 → ℝ, IsPopulation p →
      generated (conjSuperop localized) p = (p 0 - p 1) ^ 2 / 2 ∧
      generated (conjSuperop distributed) p = ((p 0 - p 1) ^ 2 + (p 2 - p 3) ^ 2) / 4) := by
  have h4 : Real.cos (Real.pi / 4) ^ 2 + Real.sin (Real.pi / 4) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have h8 : Real.cos (Real.pi / 8) ^ 2 + Real.sin (Real.pi / 8) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  have h1 : (1:ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num
  have uL := X7L_unit _ _ _ _ h4 h1
  have uD := X7L_unit _ _ _ _ h8 h8
  have rL : response localized = X7L_G (1/2) 0 := by
    rw [X7L_loc, X7L_resp _ _ _ _ h4 h1, mul_assoc, X7L_c4, X7L_s4]; norm_num
  have rD : response distributed = X7L_G (1/4) (1/4) := by
    rw [X7L_dis, X7L_resp _ _ _ _ h8 h8, X7L_cs8]
  rw [← X7L_loc] at uL
  rw [← X7L_dis] at uD
  have hD : fourthDenominator 4 = 840 := by norm_num [fourthDenominator]
  refine ⟨uL, uD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [X7J_cgp _ uL, rL, X7L_tr]; norm_num
  · rw [X7J_cgp _ uD, rD, X7L_tr]; norm_num
  · rw [X7J_cgpd2 _ uL, rL, X7L_tr, X7L_tr2, X7L_dsq]; norm_num [fourthDenominator]
  · rw [X7J_cgpd2 _ uD, rD, X7L_tr, X7L_tr2, X7L_dsq]; norm_num [fourthDenominator]
  · rw [X7J_mom2 _ uL, rL, X7L_tr, X7L_tr2, X7L_dsq]; norm_num [fourthDenominator]
  · rw [X7J_mom2 _ uD, rD, X7L_tr, X7L_tr2, X7L_dsq]; norm_num [fourthDenominator]
  · rw [rL]; ext i j; fin_cases i <;> fin_cases j <;> simp [X7L_G]
  · rw [rD]; ext i j; fin_cases i <;> fin_cases j <;> simp [X7L_G]
  · rw [rL, X7L_tr, X7L_tr2, X7L_dsq]; norm_num
  · rw [rD, X7L_tr, X7L_tr2, X7L_dsq]; norm_num
  · intro p _
    constructor
    · rw [X7L_loc, X7L_gen _ _ _ _ h4 h1, mul_assoc 2, X7L_c4, X7L_s4]; ring
    · rw [X7L_dis, X7L_gen _ _ _ _ h8 h8, X7L_cs8]; ring
