-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.dirichletMonomialMoments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:21:00.129928+00:00
-- url     : https://prove2.me/submissions/81f01662-3fc4-4e5c-9574-9203fd0ad339

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

lemma X7M_fin (d : ℕ) (hd : 1 ≤ d) (a : Fin d → ℕ) :
    (∫ p, ∏ i, p i ^ a i ∂simplexLaw (Fin d)) =
      ((Nat.factorial (d - 1) : ℝ) * ∏ i, (Nat.factorial (a i) : ℝ)) /
        (Nat.factorial (d + (∑ i, a i) - 1) : ℝ) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [X7M_main a, Fintype.card_fin]

lemma X7M_four (d : ℕ) (hd : 1 ≤ d) (a : Fin d → ℕ) (s : Finset (Fin d))
    (ha : ∀ k ∉ s, a k = 0) (hsum : ∑ k ∈ s, a k = 4) (c : ℝ)
    (hc : ∏ k ∈ s, ((a k).factorial : ℝ) = c) (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ p, ∏ k ∈ s, p k ^ a k = f p) :
    (∫ p, f p ∂simplexLaw (Fin d)) = c / fourthDenominator d := by
  have h1 : ∀ p : Fin d → ℝ, ∏ k, p k ^ a k = f p := by
    intro p
    rw [← hf, Finset.prod_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk, pow_zero]
  have h2 : ∏ k, ((a k).factorial : ℝ) = c := by
    rw [← hc, Finset.prod_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk]; simp
  have h3 : ∑ k, a k = 4 := by
    rw [← hsum, Finset.sum_subset (Finset.subset_univ s)]
    intro k _ hk; rw [ha k hk]
  simp_rw [← h1]
  rw [X7M_fin d hd, h2, h3]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [show e + 1 + 4 - 1 = e + 4 by omega, show e + 1 - 1 = e by omega]
  simp only [fourthDenominator, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  have : (0:ℝ) < e.factorial := by positivity
  field_simp
  ring

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution (d : ℕ) (hd : 1 ≤ d) :
    (∀ a : Fin d → ℕ, (∫ p, ∏ i, p i ^ a i ∂simplexLaw (Fin d)) =
      ((Nat.factorial (d - 1) : ℝ) * ∏ i, (Nat.factorial (a i) : ℝ)) /
        (Nat.factorial (d + (∑ i, a i) - 1) : ℝ)) ∧
    (∀ i : Fin d, (∫ p, p i ^ 4 ∂simplexLaw (Fin d)) = 24 / fourthDenominator d) ∧
    (∀ i j : Fin d, i ≠ j →
      (∫ p, p i ^ 3 * p j ∂simplexLaw (Fin d)) = 6 / fourthDenominator d) ∧
    (∀ i j : Fin d, i ≠ j →
      (∫ p, p i ^ 2 * p j ^ 2 ∂simplexLaw (Fin d)) = 4 / fourthDenominator d) ∧
    (∀ i j k : Fin d, i ≠ j → i ≠ k → j ≠ k →
      (∫ p, p i ^ 2 * p j * p k ∂simplexLaw (Fin d)) = 2 / fourthDenominator d) ∧
    (∀ i j k l : Fin d, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      (∫ p, p i * p j * p k * p l ∂simplexLaw (Fin d)) = 1 / fourthDenominator d) := by
  refine ⟨X7M_fin d hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact X7M_four d hd (fun k => if k = i then 4 else 0) {i}
      (by intro k hk; simp at hk; simp [hk]) (by simp) 24 (by simp; norm_num [Nat.factorial])
      _ (by intro p; simp)
  · intro i j hij
    exact X7M_four d hd (fun k => if k = i then 3 else if k = j then 1 else 0) {i, j}
      (by intro k hk; simp at hk; simp [hk.1, hk.2]) (by simp [hij, Ne.symm hij]) 6
      (by simp [hij, Ne.symm hij]; norm_num [Nat.factorial])
      _ (by intro p; simp [hij, Ne.symm hij])
  · intro i j hij
    exact X7M_four d hd (fun k => if k = i then 2 else if k = j then 2 else 0) {i, j}
      (by intro k hk; simp at hk; simp [hk.1, hk.2]) (by simp [hij, Ne.symm hij]) 4
      (by simp [hij, Ne.symm hij]; norm_num [Nat.factorial])
      _ (by intro p; simp [hij, Ne.symm hij])
  · intro i j k hij hik hjk
    exact X7M_four d hd (fun m => if m = i then 2 else if m = j then 1 else if m = k then 1 else 0)
      {i, j, k}
      (by intro m hm; simp at hm; simp [hm.1, hm.2.1, hm.2.2])
      (by simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]) 2
      (by simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk])
      _ (by intro p; simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]; ring)
  · intro i j k l hij hik hil hjk hjl hkl
    exact X7M_four d hd
      (fun m => if m = i then 1 else if m = j then 1 else if m = k then 1 else if m = l then 1 else 0)
      {i, j, k, l}
      (by intro m hm; simp at hm; simp [hm.1, hm.2.1, hm.2.2.1, hm.2.2.2])
      (by simp [hij, hik, hil, hjk, hjl, hkl, Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
        Ne.symm hjl, Ne.symm hkl]) 1
      (by simp [hij, hik, hil, hjk, hjl, hkl, Ne.symm hij, Ne.symm hik, Ne.symm hil, Ne.symm hjk,
        Ne.symm hjl, Ne.symm hkl])
      _ (by intro p; simp [hij, hik, hil, hjk, hjl, hkl, Ne.symm hij, Ne.symm hik, Ne.symm hil,
        Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]; ring)
