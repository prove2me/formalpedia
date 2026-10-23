-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.qubitLaw
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:48:15.618485+00:00
-- url     : https://prove2.me/submissions/fcc757bf-a0c7-460d-80e1-a0cd897708c4

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

lemma X7W_mon (a b : ℕ) : (∫ p, p 0 ^ a * p 1 ^ b ∂simplexLaw (Fin 2)) =
    ((a.factorial : ℝ) * b.factorial) / (a + b + 1).factorial := by
  have h := X7M_main (ι := Fin 2) ![a, b]
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fintype.card_fin] at h
  rw [h, show 2 + (a + b) - 1 = a + b + 1 by omega]
  simp

lemma X7A_ae_pop {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᵐ p ∂simplexLaw ι, IsPopulation p := by
  unfold simplexLaw
  have hs : MeasurableSet {y : ι → ℝ | IsPopulation y} := by
    have e : {y : ι → ℝ | IsPopulation y} = (⋂ i, {y | 0 ≤ y i}) ∩ {y | ∑ i, y i = 1} := by
      ext; simp [IsPopulation]
    rw [e]
    exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)
  refine (ae_map_iff X7M_norm_meas.aemeasurable hs).mpr ?_
  filter_upwards [X7M_pi_pos] with z hz
  have hS : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  simp only [Set.mem_setOf_eq, normalizePopulation, hS.ne', if_false]
  refine ⟨fun i => div_nonneg (hz i).le hS.le, ?_⟩
  rw [← Finset.sum_div, div_self hS.ne']

lemma X7Q_int (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    (f : ℝ → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (by filter_upwards [hμ] with x hx; exact hC x hx)

lemma X7Q_det (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Icc a b)
    (h : ∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) : μ = ν := by
  have hP : ∀ P : Polynomial ℝ, ∫ x, P.eval x ∂μ = ∫ x, P.eval x ∂ν := by
    intro P
    simp_rw [Polynomial.eval_eq_sum_range]
    rw [integral_finsetSum _ fun i _ => (X7Q_int μ a b hμ _ (continuous_pow i)).const_mul _,
      integral_finsetSum _ fun i _ => (X7Q_int ν a b hν _ (continuous_pow i)).const_mul _]
    simp_rw [integral_const_mul, h]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have approx : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Icc a b) →
      ∀ (P : Polynomial ℝ) (ε : ℝ), (∀ x ∈ Icc a b, |P.eval x - f x| < ε) →
      ‖∫ x, f x ∂ρ - ∫ x, P.eval x ∂ρ‖ ≤ ε * ρ.real univ := by
    intro ρ _ hρ P ε hPε
    rw [← integral_sub (f.integrable ρ) (X7Q_int ρ a b hρ _ P.continuous)]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hρ] with x hx
    rw [Real.norm_eq_abs, abs_sub_comm]; exact (hPε x hx).le
  have key : ∀ ε > 0, |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ε * (μ.real univ + ν.real univ) := by
    intro ε hε
    obtain ⟨P, hPε⟩ := exists_polynomial_near_of_continuousOn a b f f.continuous.continuousOn ε hε
    have h1 := approx μ hμ P ε hPε
    have h2 := approx ν hν P ε hPε
    rw [hP P] at h1
    rw [Real.norm_eq_abs] at h1 h2
    calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
        = |(∫ x, f x ∂μ - ∫ x, P.eval x ∂ν) - (∫ x, f x ∂ν - ∫ x, P.eval x ∂ν)| := by ring_nf
      _ ≤ |∫ x, f x ∂μ - ∫ x, P.eval x ∂ν| + |∫ x, f x ∂ν - ∫ x, P.eval x ∂ν| := abs_sub _ _
      _ ≤ ε * μ.real univ + ε * ν.real univ := add_le_add h1 h2
      _ = _ := by ring
  by_contra hne
  have hD : 0 < |∫ x, f x ∂μ - ∫ x, f x ∂ν| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set D := |∫ x, f x ∂μ - ∫ x, f x ∂ν|
  set S := μ.real univ + ν.real univ
  have hS : 0 ≤ S := by positivity
  have := key (D / (2 * (S + 1))) (by positivity)
  have : D / (2 * (S + 1)) * S < D := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

lemma X7Q_ftc (g m : ℝ) (hg : 0 < g) (hm : 0 ≤ m) :
    IntegrableOn (fun x => 1 / (2 * Real.sqrt (g * x))) (Ioc 0 m) ∧
    ∫ x in Ioc 0 m, 1 / (2 * Real.sqrt (g * x)) = Real.sqrt (m / g) := by
  have hcont : ContinuousOn (fun x => Real.sqrt (x / g)) (Icc 0 m) := by fun_prop
  have hder : ∀ x ∈ Ioo 0 m, HasDerivAt (fun x => Real.sqrt (x / g)) (1 / (2 * Real.sqrt (g * x))) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h := ((hasDerivAt_id x).div_const g).sqrt (ne_of_gt (div_pos hx0 hg))
    have h' : HasDerivAt (fun x => Real.sqrt (x / g)) (1 / g / (2 * Real.sqrt (x / g))) x := h
    have e : Real.sqrt (g * x) = g * Real.sqrt (x / g) := by
      rw [show g * x = g ^ 2 * (x / g) by field_simp, Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg.le]
    convert h' using 1
    rw [e]; field_simp
  have hpos : ∀ x ∈ Ioo 0 m, 0 ≤ 1 / (2 * Real.sqrt (g * x)) := fun x _ => by positivity
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont hder hpos
  refine ⟨hint, ?_⟩
  rw [← intervalIntegral.integral_of_le hm, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hm hcont hder
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hm).mpr hint)]
  simp

/-- the CDF of the target density. -/
lemma X7Q_dens (g a : ℝ) (hg : 0 < g) :
    ∫⁻ x in Iic a, ENNReal.ofReal (if 0 < x ∧ x < g then 1 / (2 * Real.sqrt (g * x)) else 0) =
      ENNReal.ofReal (Real.sqrt (min a g / g)) := by
  set k : ℝ → ℝ := fun x => 1 / (2 * Real.sqrt (g * x))
  have hf : (fun x => ENNReal.ofReal (if 0 < x ∧ x < g then k x else 0)) =
      (Ioo 0 g).indicator (fun x => ENNReal.ofReal (k x)) := by
    funext x; simp only [indicator, mem_Ioo]; split_ifs <;> simp
  rw [hf, setLIntegral_indicator measurableSet_Ioo]
  rcases lt_or_ge a 0 with ha | ha
  · have : min a g / g < 0 := div_neg_of_neg_of_pos (lt_of_le_of_lt (min_le_left _ _) ha) hg
    rw [Real.sqrt_eq_zero'.mpr this.le, ENNReal.ofReal_zero]
    have he : Ioo 0 g ∩ Iic a = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]
      intro ⟨⟨h1, _⟩, h2⟩; linarith
    rw [he, Measure.restrict_empty, lintegral_zero_measure]
  · set m := min a g
    have hm : 0 ≤ m := le_min ha hg.le
    have hae : (Ioo 0 g ∩ Iic a : Set ℝ) =ᵐ[volume] Ioc 0 m := by
      rcases lt_or_ge a g with hag | hag
      · have : m = a := min_eq_left hag.le
        rw [this]
        refine Filter.EventuallyEq.of_eq (Set.ext fun x => ?_)
        simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
      · have : m = g := min_eq_right hag
        rw [this]
        have e : (Ioo 0 g ∩ Iic a : Set ℝ) = Ioo 0 g := by
          ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]
          constructor
          · rintro ⟨h, _⟩; exact h
          · rintro h; exact ⟨h, by linarith [h.2]⟩
        rw [e]; exact Ioo_ae_eq_Ioc
    rw [setLIntegral_congr hae]
    obtain ⟨hint, hval⟩ := X7Q_ftc g m hg hm
    rw [← ofReal_integral_eq_lintegral_ofReal hint, hval]
    filter_upwards with x
    simp only [Pi.zero_apply, k]; positivity

lemma X7Q_push (g a : ℝ) (hg : 0 < g) :
    Measure.map (fun u : ℝ => g * (2 * u - 1) ^ 2) (volume.restrict (Icc (0:ℝ) 1)) (Iic a) =
      ENNReal.ofReal (Real.sqrt (min a g / g)) := by
  have hmeas : Measurable (fun u : ℝ => g * (2 * u - 1) ^ 2) := by fun_prop
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply (hmeas measurableSet_Iic)]
  rcases lt_or_ge a 0 with ha | ha
  · have : min a g / g < 0 := div_neg_of_neg_of_pos (lt_of_le_of_lt (min_le_left _ _) ha) hg
    rw [Real.sqrt_eq_zero'.mpr this.le, ENNReal.ofReal_zero]
    have he : (fun u : ℝ => g * (2 * u - 1) ^ 2) ⁻¹' Iic a ∩ Icc 0 1 = ∅ := by
      ext u; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro ⟨h1, _⟩; nlinarith [sq_nonneg (2 * u - 1)]
    rw [he, measure_empty]
  · set m := min a g
    have hm : 0 ≤ m := le_min ha hg.le
    have hmg : m ≤ g := min_le_right _ _
    have hma : m ≤ a := min_le_left _ _
    set r := Real.sqrt (m / g)
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = m / g := Real.sq_sqrt (div_nonneg hm hg.le)
    have hgr : g * r ^ 2 = m := by rw [hr2]; field_simp
    have hr1 : r ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by rw [div_le_one hg]; exact hmg)
    have e : (fun u : ℝ => g * (2 * u - 1) ^ 2) ⁻¹' Iic a ∩ Icc 0 1 = Icc ((1 - r) / 2) ((1 + r) / 2) := by
      ext u; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hq : (2 * u - 1) ^ 2 ≤ 1 := by nlinarith
        have hle : g * (2 * u - 1) ^ 2 ≤ m := le_min h1 (by nlinarith)
        have hsq : (2 * u - 1) ^ 2 ≤ r ^ 2 := by
          have := mul_le_mul_of_nonneg_left (le_refl g) hg.le
          nlinarith
        constructor <;> nlinarith
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith, by linarith⟩
        have : (2 * u - 1) ^ 2 ≤ r ^ 2 := by nlinarith
        nlinarith
    rw [e, Real.volume_Icc]
    congr 1; ring

lemma X7Q_law (g : ℝ) (hg : 0 < g) :
    Measure.map (fun u : ℝ => g * (2 * u - 1) ^ 2) (volume.restrict (Icc (0:ℝ) 1)) =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (if 0 < x ∧ x < g then 1 / (2 * Real.sqrt (g * x)) else 0)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [X7Q_push g a hg, withDensity_apply _ measurableSet_Iic, X7Q_dens g a hg]

lemma X7Q_unif : Measure.map (fun p : Fin 2 → ℝ => p 0) (simplexLaw (Fin 2)) =
    volume.restrict (Icc (0:ℝ) 1) := by
  have hm0 : Measurable (fun p : Fin 2 → ℝ => p 0) := measurable_pi_apply 0
  haveI : IsProbabilityMeasure (Measure.map (fun p : Fin 2 → ℝ => p 0) (simplexLaw (Fin 2))) :=
    Measure.isProbabilityMeasure_map hm0.aemeasurable
  haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 1)) := isFiniteMeasure_restrict.mpr (by simp)
  refine X7Q_det _ _ 0 1 ?_ ?_ ?_
  · refine (ae_map_iff (p := fun x : ℝ => x ∈ Icc (0:ℝ) 1) hm0.aemeasurable measurableSet_Icc).mpr ?_
    filter_upwards [X7J_ae_cube] with p hp
    exact hp 0 (mem_univ _)
  · exact ae_restrict_mem measurableSet_Icc
  · intro k
    rw [integral_map hm0.aemeasurable (continuous_pow k).aestronglyMeasurable]
    have h := X7W_mon k 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero] at h
    rw [h, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, integral_pow,
      Nat.factorial_succ]
    push_cast
    have : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    field_simp
    simp

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let E := conjSuperop U
    let xmax := 3 * cgp E
    (0 < cgp E → coherenceLaw E = volume.withDensity (fun x : ℝ =>
      ENNReal.ofReal (if 0 < x ∧ x < xmax then 1 / (2 * Real.sqrt (xmax * x)) else 0))) ∧
    (cgp E = 0 → coherenceLaw E = Measure.dirac 0) := by
  intro E xmax
  set G := response U with hG
  set g := G 0 0
  have hrow := X7J_rowsum U hU
  have h01 : G 0 1 = -g := by
    have := hrow 0; simp only [Fin.sum_univ_two] at this; linarith
  have h10 : G 1 0 = -g := by
    have := congrFun (congrFun (X7J_symm U) 0) 1
    simp only [Matrix.transpose_apply] at this
    exact this.trans h01
  have h11 : G 1 1 = g := by
    have := hrow 1; simp only [Fin.sum_univ_two] at this; linarith
  have hgen : ∀ p, generated E p = g * (p 0 - p 1) ^ 2 := by
    intro p
    rw [X7J_genquad U hU]
    simp only [quadratic, Fin.sum_univ_two, ← hG, h01, h10, h11]
    ring
  have hcgp : cgp E = g / 3 := by
    rw [X7J_cgp U hU]
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, ← hG, h11, Fintype.card_fin]
    ring
  have hxmax : xmax = g := by simp only [xmax, hcgp]; ring
  have hlaw : coherenceLaw E = Measure.map (fun u : ℝ => g * (2 * u - 1) ^ 2)
      (volume.restrict (Icc (0:ℝ) 1)) := by
    have hm0 : Measurable (fun p : Fin 2 → ℝ => p 0) := measurable_pi_apply 0
    rw [← X7Q_unif, Measure.map_map (by fun_prop : Measurable fun u : ℝ => g * (2 * u - 1) ^ 2) hm0]
    unfold coherenceLaw
    refine Measure.map_congr ?_
    filter_upwards [X7A_ae_pop] with p hp
    have hs := hp.2
    simp only [Fin.sum_univ_two] at hs
    simp only [Function.comp, hgen]
    rw [show p 1 = 1 - p 0 by linarith]
    ring_nf
  refine ⟨fun hpos => ?_, fun hz => ?_⟩
  · have hg : 0 < g := by rw [hcgp] at hpos; linarith
    rw [hlaw, X7Q_law g hg, hxmax]
  · have hg : g = 0 := by rw [hcgp] at hz; linarith
    have : generated E = fun _ => (0:ℝ) := by funext p; rw [hgen, hg, zero_mul]
    unfold coherenceLaw
    rw [this, Measure.map_const, measure_univ, one_smul]
