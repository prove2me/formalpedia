-- Prove2me | solution 1 for PreorderADI.Correlation.newsvendor_order_and_profit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:46:42.717458+00:00
-- url     : https://prove2.me/submissions/c4a11c8c-3b4b-43c0-a89f-912a7d744584

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

open Filter Topology Set

lemma aux_nvop_min_le (Q Q' y : ℝ) :
    min Q y - min Q' y ≤ (Ioi Q').indicator (fun _ => Q - Q') y := by
  by_cases hy : Q' < y
  · rw [indicator_of_mem (show y ∈ Ioi Q' from hy), min_eq_left hy.le]
    linarith [min_le_left Q y]
  · rw [indicator_of_notMem (show y ∉ Ioi Q' from hy)]
    push Not at hy
    rw [min_eq_right hy]
    linarith [min_le_right Q y]

lemma aux_nvop_min_lt (Q Q' y : ℝ) (hy : y ∈ Ioo (min Q Q') (max Q Q')) :
    min Q y - min Q' y < (Ioi Q').indicator (fun _ => Q - Q') y := by
  rcases hy with ⟨h1, h2⟩
  rcases lt_or_ge Q Q' with h | h
  · rw [min_eq_left h.le] at h1
    rw [max_eq_right h.le] at h2
    rw [indicator_of_notMem (show y ∉ Ioi Q' from fun hh => by simp at hh; linarith),
      min_eq_left h1.le, min_eq_right h2.le]
    linarith
  · rcases h.lt_or_eq with h | h
    · rw [min_eq_right h.le] at h1
      rw [max_eq_left h.le] at h2
      rw [indicator_of_mem (show y ∈ Ioi Q' from h1), min_eq_right h2.le, min_eq_left h1.le]
      linarith
    · subst h
      simp at h1 h2
      linarith

lemma aux_nvop_map (μ s : ℝ) :
    (gaussianReal 0 1).map (fun t => μ + s * t) = gaussianReal μ (Real.toNNReal (s ^ 2)) := by
  have : (fun t : ℝ => μ + s * t) = (fun u => μ + u) ∘ (fun t => s * t) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · ext; simp [sq_nonneg]

lemma aux_nvop_int_min (μ : ℝ) (v : NNReal) (Q : ℝ) :
    Integrable (fun y => min Q y) (gaussianReal μ v) := by
  have hid : Integrable (fun y : ℝ => y) (gaussianReal μ v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  refine Integrable.mono' ((integrable_const |Q|).add hid.abs) (by fun_prop) ?_
  exact Eventually.of_forall (fun y => by
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rcases le_total Q y with h | h
    · rw [min_eq_left h]; linarith [abs_nonneg y]
    · rw [min_eq_right h]; linarith [abs_nonneg Q])

lemma aux_nvop_eq (P : Params) (ρ x Q : ℝ) :
    expectedSecondProfit P ρ x Q = P.vL * ∫ y, min Q y ∂(lowDemandLaw P ρ x) - P.c * Q := by
  unfold expectedSecondProfit lowDemandLaw
  rw [integral_sub ((aux_nvop_int_min _ _ Q).const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp

lemma aux_nvop_pdf (t : ℝ) :
    gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
  simp [gaussianPDFReal]

lemma aux_nvop_Iic (z : ℝ) :
    ∫ t in Iic z, t ∂(gaussianReal 0 1) = - gaussianPDFReal 0 1 z := by
  set K := (Real.sqrt (2 * Real.pi))⁻¹
  have h1 : ∫ t in Iic z, t ∂(gaussianReal 0 1) = ∫ t in Iic z, K * Real.exp (-t ^ 2 / 2) * t := by
    rw [← integral_indicator measurableSet_Iic, integral_gaussianReal_eq_integral_smul one_ne_zero,
      ← integral_indicator measurableSet_Iic]
    congr 1
    funext t
    by_cases ht : t ∈ Iic z
    · simp [ht, aux_nvop_pdf, K]
    · simp [ht]
  rw [h1, aux_nvop_pdf]
  have hderiv : ∀ t ∈ Iio z, HasDerivAt (fun t : ℝ => -K * Real.exp (-t ^ 2 / 2))
      (K * Real.exp (-t ^ 2 / 2) * t) t := by
    intro t _
    have h0 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-t) t := by
      have := ((hasDerivAt_pow 2 t).neg).div_const 2
      exact this.congr_deriv (by norm_num; ring)
    exact (h0.exp.const_mul (-K)).congr_deriv (by ring)
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-t ^ 2 / 2) * t) (Iic z) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul K
    refine (this.congr (Eventually.of_forall fun t => ?_)).integrableOn
    simp only
    rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
    ring
  have htend : Tendsto (fun t : ℝ => -K * Real.exp (-t ^ 2 / 2)) atBot (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ 2) atBot atTop := by
      have := (tendsto_pow_atTop (α := ℝ) (two_ne_zero)).comp tendsto_neg_atBot_atTop
      refine this.congr (fun t => by simp)
    have h2 : Tendsto (fun t : ℝ => -t ^ 2 / 2) atBot atBot :=
      (tendsto_neg_atTop_atBot.comp h1).atBot_div_const two_pos
    have := ((Real.tendsto_exp_atBot.comp h2).const_mul (-K))
    simpa using this
  have := integral_Iic_of_hasDerivAt_of_tendsto (by fun_prop) hderiv hint htend
  rw [this]
  ring

lemma aux_nvop_minint (z : ℝ) :
    ∫ t, min z t ∂(gaussianReal 0 1) = - gaussianPDFReal 0 1 z + (1 - stdNormalCdf z) * z := by
  have hint := aux_nvop_int_min 0 1 z
  rw [← integral_add_compl (measurableSet_Iic (a := z)) hint, compl_Iic]
  have e1 : ∫ t in Iic z, min z t ∂(gaussianReal 0 1) = ∫ t in Iic z, t ∂(gaussianReal 0 1) :=
    setIntegral_congr_fun measurableSet_Iic (fun t ht => min_eq_right ht)
  have e2 : ∫ t in Ioi z, min z t ∂(gaussianReal 0 1) = ∫ t in Ioi z, z ∂(gaussianReal 0 1) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => min_eq_left (le_of_lt ht))
  rw [e1, e2, aux_nvop_Iic, setIntegral_const, smul_eq_mul, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic, stdNormalCdf, cdf_eq_real]

end PreorderADI.Correlation

open PreorderADI.Correlation

theorem solution (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) (x : ℝ) :
    (∀ Q : ℝ, expectedSecondProfit P ρ x Q ≤ expectedSecondProfit P ρ x (orderQty P ρ x)) ∧
    (∀ Q : ℝ, (∀ Q' : ℝ, expectedSecondProfit P ρ x Q' ≤ expectedSecondProfit P ρ x Q) →
      Q = orderQty P ρ x) ∧
    expectedSecondProfit P ρ x (orderQty P ρ x) = secondProfit P ρ x := by
  obtain ⟨hρ0, hρ1⟩ := hρ
  have hs : 0 < lowSd P ρ := by
    unfold lowSd
    apply mul_pos hP.sigmaL_pos
    apply Real.sqrt_pos.mpr
    nlinarith
  have hvL : 0 < P.vL := hP.c_pos.trans hP.c_lt_vL
  have hf : ∀ Q, expectedSecondProfit P ρ x Q
      = P.vL * ∫ y, min Q y ∂(lowDemandLaw P ρ x) - P.c * Q := aux_nvop_eq P ρ x
  set μ := lowMean P ρ x with hμ
  set s := lowSd P ρ with hsdef
  set Qs := orderQty P ρ x with hQs
  have hQs' : Qs = μ + s * P.zL := by rw [hQs, orderQty]; ring
  set N := lowDemandLaw P ρ x with hN
  have hNg : N = gaussianReal μ (Real.toNNReal (s ^ 2)) := rfl
  have : IsProbabilityMeasure N := by rw [hNg]; infer_instance
  have hNint : ∀ Q, Integrable (fun y => min Q y) N := fun Q => by
    rw [hNg]; exact aux_nvop_int_min _ _ Q
  have hv : Real.toNNReal (s ^ 2) ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    positivity
  have hNmap : N = (gaussianReal 0 1).map (fun t => μ + s * t) := by
    rw [aux_nvop_map, hNg]
  have hIic : N.real (Set.Iic Qs) = stdNormalCdf P.zL := by
    rw [stdNormalCdf, cdf_eq_real, hNmap, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext t
    simp only [Set.mem_preimage, Set.mem_Iic, hQs']
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hIoi : N.real (Set.Ioi Qs) = P.c / P.vL := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, hIic, hP.zL_spec]
    field_simp
    ring
  have hdiff : ∀ Q, ∫ y, min Q y ∂N - ∫ y, min Qs y ∂N ≤ P.c / P.vL * (Q - Qs) := by
    intro Q
    rw [← integral_sub (hNint Q) (hNint Qs), ← hIoi, ← smul_eq_mul,
      ← integral_indicator_const _ measurableSet_Ioi]
    exact integral_mono ((hNint Q).sub (hNint Qs))
      ((integrable_const _).indicator measurableSet_Ioi) (fun y => aux_nvop_min_le Q Qs y)
  have hdiff_lt : ∀ Q, Q ≠ Qs →
      ∫ y, min Q y ∂N - ∫ y, min Qs y ∂N < P.c / P.vL * (Q - Qs) := by
    intro Q hQ
    have hI : Integrable (fun y => (Set.Ioi Qs).indicator (fun _ => Q - Qs) y) N :=
      (integrable_const _).indicator measurableSet_Ioi
    have hD : Integrable (fun y => min Q y - min Qs y) N := (hNint Q).sub (hNint Qs)
    rw [← integral_sub (hNint Q) (hNint Qs), ← hIoi, ← smul_eq_mul,
      ← integral_indicator_const _ measurableSet_Ioi, ← sub_pos,
      ← integral_sub hI hD]
    rw [integral_pos_iff_support_of_nonneg (fun y => sub_nonneg.mpr (aux_nvop_min_le Q Qs y))
      (hI.sub hD)]
    refine lt_of_lt_of_le ?_ (measure_mono (s := Set.Ioo (min Q Qs) (max Q Qs)) ?_)
    · rw [pos_iff_ne_zero]
      intro h0
      rw [hNg] at h0
      have h1 := gaussianReal_absolutelyContinuous' μ hv h0
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h1
      have := min_lt_max.mpr hQ
      linarith
    · intro y hy
      rw [Function.mem_support]
      exact (sub_pos.mpr (aux_nvop_min_lt Q Qs y hy)).ne'
  refine ⟨?_, ?_, ?_⟩
  · intro Q
    rw [hf, hf]
    have key : P.vL * (∫ y, min Q y ∂N - ∫ y, min Qs y ∂N) ≤ P.c * (Q - Qs) := by
      calc P.vL * (∫ y, min Q y ∂N - ∫ y, min Qs y ∂N)
          ≤ P.vL * (P.c / P.vL * (Q - Qs)) := mul_le_mul_of_nonneg_left (hdiff Q) hvL.le
        _ = P.c * (Q - Qs) := by field_simp
    rw [mul_sub, mul_sub] at key
    linarith
  · intro Q hQ
    by_contra hne
    have key : P.vL * (∫ y, min Q y ∂N - ∫ y, min Qs y ∂N) < P.c * (Q - Qs) := by
      calc P.vL * (∫ y, min Q y ∂N - ∫ y, min Qs y ∂N)
          < P.vL * (P.c / P.vL * (Q - Qs)) := mul_lt_mul_of_pos_left (hdiff_lt Q hne) hvL
        _ = P.c * (Q - Qs) := by field_simp
    have h2 := hQ Qs
    rw [hf, hf] at h2
    rw [mul_sub, mul_sub] at key
    linarith
  · have hclosed : ∫ y, min Qs y ∂N = μ + s * ∫ t, min P.zL t ∂(gaussianReal 0 1) := by
      rw [hNmap, integral_map (by fun_prop) (show Continuous (fun y : ℝ => min Qs y) by fun_prop).aestronglyMeasurable]
      have hpt : ∀ t, min Qs (μ + s * t) = μ + s * min P.zL t := by
        intro t
        rw [hQs']
        rcases le_total P.zL t with h | h
        · rw [min_eq_left h, min_eq_left (by nlinarith)]
        · rw [min_eq_right h, min_eq_right (by nlinarith)]
      simp_rw [hpt]
      rw [integral_add (integrable_const _) ((aux_nvop_int_min 0 1 P.zL).const_mul s),
        integral_const, integral_const_mul]
      simp
    rw [hf, hclosed, aux_nvop_minint, hP.zL_spec, hQs']
    unfold secondProfit stdNormalPdf
    rw [hμ, hsdef]
    unfold lowMean lowSd
    field_simp
    ring
