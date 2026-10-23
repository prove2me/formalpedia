-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.universalBound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:00:48.641043+00:00
-- url     : https://prove2.me/submissions/b6255b7b-3d49-4a98-a9d8-212fc0f36bca

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

def X7H_U : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + Complex.I) / 2, (1 - Complex.I) / 2; (1 - Complex.I) / 2, (1 + Complex.I) / 2]

lemma X7H_unitary : X7H_U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7H_U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf

lemma X7H_trans (i j : Fin 2) : transition X7H_U i j = 1 / 2 := by
  fin_cases i <;> fin_cases j <;> simp [transition, X7H_U, Complex.normSq_apply] <;> norm_num

lemma X7H_resp (i j : Fin 2) : response X7H_U i j = (if i = j then 1 else 0) - 1 / 2 := by
  simp only [response, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    X7H_trans, Fin.sum_univ_two]
  norm_num

lemma X7H_zsp {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    zeroSumProjector ι i j = 1 - 1 / (Fintype.card ι : ℝ) := rfl

lemma X7H_aniso (i j : Fin 2) : anisotropy (response X7H_U) i j = if i = j then 0 else -1 := by
  have htr : (response X7H_U).trace = 1 := by
    simp [Matrix.trace, Fin.sum_univ_two, X7H_resp]; norm_num
  simp only [anisotropy, Matrix.sub_apply, Matrix.smul_apply, htr, X7H_resp, X7H_zsp,
    Fintype.card_fin, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

lemma X7H_excess_sq : excess (response X7H_U) ^ 2 = 1 / 30 := by
  rw [excess, Real.sq_sqrt (by
    apply div_nonneg
    · unfold realFrobeniusSq diagonalSq; positivity
    · unfold fourthDenominator; positivity)]
  simp [realFrobeniusSq, diagonalSq, Fin.sum_univ_two, X7H_aniso, fourthDenominator]
  norm_num


lemma X7W_gen (p : Fin 2 → ℝ) : generated (conjSuperop X7H_U) p = (p 0 - p 1) ^ 2 / 2 := by
  simp only [generated, coherence, conjSuperop, inputDensity, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, X7H_U]
  simp [Complex.normSq_apply, Fin.sum_univ_two]
  ring

lemma X7W_mon (a b : ℕ) : (∫ p, p 0 ^ a * p 1 ^ b ∂simplexLaw (Fin 2)) =
    ((a.factorial : ℝ) * b.factorial) / (a + b + 1).factorial := by
  have h := X7M_main (ι := Fin 2) ![a, b]
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fintype.card_fin] at h
  rw [h, show 2 + (a + b) - 1 = a + b + 1 by omega]
  simp

lemma X7W_mon_int (a b : ℕ) : Integrable (fun p : Fin 2 → ℝ => p 0 ^ a * p 1 ^ b) (simplexLaw (Fin 2)) :=
  Integrable.of_integral_ne_zero (by rw [X7W_mon]; positivity)

lemma X7W_poly {n : ℕ} (c : Fin n → ℝ) (a b : Fin n → ℕ) :
    (∫ p, ∑ k, c k * (p 0 ^ a k * p 1 ^ b k) ∂simplexLaw (Fin 2)) =
      ∑ k, c k * (((a k).factorial : ℝ) * (b k).factorial / (a k + b k + 1).factorial) := by
  rw [integral_finsetSum _ fun k _ => (X7W_mon_int (a k) (b k)).const_mul (c k)]
  simp only [integral_const_mul, X7W_mon]

lemma X7W_cgp : cgp (conjSuperop X7H_U) = 1 / 6 := by
  have h : ∀ p : Fin 2 → ℝ, generated (conjSuperop X7H_U) p ^ 1 =
      ∑ k : Fin 3, ![1/2, -1, 1/2] k * (p 0 ^ ![2, 1, 0] k * p 1 ^ ![0, 1, 2] k) := by
    intro p; rw [X7W_gen]; simp [Fin.sum_univ_succ]; ring
  simp only [cgp, moment, h, X7W_poly]
  simp [Fin.sum_univ_succ, Nat.factorial]; norm_num

lemma X7W_var : coherenceVariance (conjSuperop X7H_U) = 1 / 45 := by
  have h : ∀ p : Fin 2 → ℝ, (generated (conjSuperop X7H_U) p - cgp (conjSuperop X7H_U)) ^ 2 =
      ∑ k : Fin 9, ![1/4, -1, 3/2, -1, 1/4, -1/6, 1/3, -1/6, 1/36] k *
        (p 0 ^ ![4, 3, 2, 1, 0, 2, 1, 0, 0] k * p 1 ^ ![0, 1, 2, 3, 4, 0, 1, 2, 0] k) := by
    intro p; rw [X7W_gen, X7W_cgp]; simp [Fin.sum_univ_succ]; ring
  simp only [coherenceVariance, h, X7W_poly]
  simp [Fin.sum_univ_succ, Nat.factorial]; norm_num

lemma X7W_cgpd : cgpd (conjSuperop X7H_U) = Real.sqrt (1 / 45) := by
  rw [cgpd, X7W_var]

lemma X7W_gamma : gammaFactor 2 = 4 / Real.sqrt 20 := by
  rw [gammaFactor]; norm_num

/-- the equality case `Δ = γ₂ C`. -/
lemma X7W_eq : cgpd (conjSuperop X7H_U) = gammaFactor 2 * cgp (conjSuperop X7H_U) := by
  rw [X7W_cgpd, X7W_gamma, X7W_cgp]
  rw [show (4 / Real.sqrt 20 * (1 / 6) : ℝ) = Real.sqrt (1 / 45) by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]; norm_num]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 2 ≤ Fintype.card ι)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ),
    gammaFactor (Fintype.card ι) * cgp (conjSuperop U) ≤ cgpd (conjSuperop U) ∧
    (0 < cgp (conjSuperop U) →
      (cgpd (conjSuperop U) = gammaFactor (Fintype.card ι) * cgp (conjSuperop U) ↔
        ∃ a : ℝ, 0 < a ∧ response U = a • zeroSumProjector ι))) := by
  intro h
  have h2 := (@h (Fin 2) _ _ (by simp) X7H_U X7H_unitary).2 (by rw [X7W_cgp]; norm_num)
  simp only [Fintype.card_fin] at h2
  obtain ⟨a, _, ha⟩ := h2.mp X7W_eq
  have h00 := congrFun (congrFun ha 0) 0
  have h01 := congrFun (congrFun ha 0) 1
  simp only [Matrix.smul_apply, X7H_resp, X7H_zsp, Fintype.card_fin, smul_eq_mul] at h00 h01
  norm_num at h00 h01
  linarith
