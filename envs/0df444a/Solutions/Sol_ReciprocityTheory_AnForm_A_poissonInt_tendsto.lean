-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonInt_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:55.738347+00:00
-- url     : https://prove2.me/submissions/2d96b38e-30bb-40c8-89ec-e4887be05a7d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonKernel_zero_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_circleAverage_poissonKernel_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ sphere (0 : ℂ) r) :
    Tendsto (poissonInt g r) (𝓝[ball 0 r] ζ₀) (𝓝 (g ζ₀)) := by
  have hζ : ‖ζ₀‖ = r := mem_sphere_zero_iff_norm.mp hζ₀
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M :=
    (isCompact_sphere 0 r).exists_bound_of_continuousOn (hg.sub continuousOn_const)
  obtain ⟨M', hM'⟩ : ∃ M', M' = max M 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M' := by rw [hM']; exact le_max_right _ _
  have hMM : ∀ z ∈ sphere (0 : ℂ) r, ‖g z - g ζ₀‖ ≤ M' := by
    intro z hz
    rw [hM']
    exact (hM z hz).trans (le_max_left _ _)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.continuousOn_iff.mp hg ζ₀ hζ₀ (ε / 2) (half_pos hε)
  have hq : 0 < (η / 2) ^ 2 := pow_pos (half_pos hη) 2
  have hden : 0 < 8 * r * (M' + 1) := mul_pos (mul_pos (by norm_num) hr) (by linarith)
  refine ⟨min (η / 2) (ε * (η / 2) ^ 2 / (8 * r * (M' + 1))),
    lt_min (half_pos hη) (div_pos (mul_pos hε hq) hden), ?_⟩
  intro w hw hwd
  have hwb : ‖w‖ < r := mem_ball_zero_iff.mp hw
  have hδ1 : dist w ζ₀ < η / 2 := lt_of_lt_of_le hwd (min_le_left _ _)
  have hδ2 : dist w ζ₀ < ε * (η / 2) ^ 2 / (8 * r * (M' + 1)) :=
    lt_of_lt_of_le hwd (min_le_right _ _)
  have hnum : 0 ≤ r ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  obtain ⟨K, hK⟩ : ∃ K, K = M' * ((r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg hM0 (div_nonneg hnum hq.le)
  have hd : r - ‖w‖ ≤ dist w ζ₀ := by
    rw [dist_comm, dist_eq_norm, ← hζ]
    exact norm_sub_norm_le ζ₀ w
  have hnum2 : r ^ 2 - ‖w‖ ^ 2 ≤ 2 * r * dist w ζ₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * r),
      sq_nonneg (r - ‖w‖), norm_nonneg w]
  have hd2 : dist w ζ₀ * (8 * r * (M' + 1)) < ε * (η / 2) ^ 2 := by
    first
    | exact (lt_div_iff₀ hden).mp hδ2
    | exact (lt_div_iff hden).mp hδ2
  have hKq : K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := by
    rw [hK, mul_assoc, div_mul_cancel₀ _ hq.ne']
  have hKlt : K < ε / 2 := by
    have h1 : M' * (r ^ 2 - ‖w‖ ^ 2) ≤ (M' + 1) * (2 * r * dist w ζ₀) := by
      have e1 := mul_le_mul_of_nonneg_left hnum2 hM0
      have e2 : 0 ≤ 2 * r * dist w ζ₀ := by positivity
      nlinarith [e1, e2]
    have h2 : K * (η / 2) ^ 2 < ε / 2 * (η / 2) ^ 2 := by
      calc K * (η / 2) ^ 2 = M' * (r ^ 2 - ‖w‖ ^ 2) := hKq
        _ ≤ (M' + 1) * (2 * r * dist w ζ₀) := h1
        _ = dist w ζ₀ * (8 * r * (M' + 1)) / 4 := by ring
        _ < ε * (η / 2) ^ 2 / 4 := by linarith
        _ ≤ ε / 2 * (η / 2) ^ 2 := by nlinarith [mul_pos hε hq]
    exact lt_of_mul_lt_mul_right h2 hq.le
  have hpt : ∀ z ∈ sphere (0 : ℂ) r,
      ‖poissonKernel 0 w z * (g z - g ζ₀)‖ ≤ ε / 2 * poissonKernel 0 w z + K := by
    intro z hz
    have hP0 := poissonKernel_zero_nonneg hw hz
    rw [norm_mul, Real.norm_of_nonneg hP0]
    by_cases hzη : dist z ζ₀ < η
    · have h3 := hgη z hz hzη
      rw [dist_eq_norm] at h3
      have h4 := mul_le_mul_of_nonneg_left h3.le hP0
      linarith
    · push_neg at hzη
      have hzw : η / 2 ≤ ‖z - w‖ := by
        have h5 := dist_triangle z w ζ₀
        rw [dist_eq_norm z w] at h5
        linarith
      have hPle := poissonKernel_zero_le hw hz (half_pos hη) hzw
      have hgM := hMM z hz
      have h6 : poissonKernel 0 w z * ‖g z - g ζ₀‖ ≤
          (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' :=
        mul_le_mul hPle hgM (norm_nonneg _) (div_nonneg hnum hq.le)
      have h7 : (r ^ 2 - ‖w‖ ^ 2) / (η / 2) ^ 2 * M' = K := by rw [hK]; ring
      have h8 : 0 ≤ ε / 2 * poissonKernel 0 w z := mul_nonneg (half_pos hε).le hP0
      linarith
  have hPi : IntervalIntegrable (fun θ : ℝ ↦ poissonKernel 0 w (circleMap 0 r θ))
      MeasureTheory.volume 0 (2 * π) :=
    (poissonKernel_zero_continuousOn hr hw).circleIntegrable hr.le
  have hPint : ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ) = 2 * π := by
    have h1 := circleAverage_poissonKernel_zero (r := r) hw
    unfold Real.circleAverage at h1
    rw [smul_eq_mul] at h1
    calc ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)
        = (2 * π) * ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, poissonKernel 0 w (circleMap 0 r θ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ = 2 * π := by rw [h1, mul_one]
  have hbound : ‖∫ θ in (0 : ℝ)..2 * π,
      poissonKernel 0 w (circleMap 0 r θ) * (g (circleMap 0 r θ) - g ζ₀)‖ ≤
      ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by positivity) ?_ ?_
    · first
      | exact Filter.Eventually.of_forall (fun θ _ ↦ hpt _ (circleMap_mem_sphere 0 hr.le θ))
      | exact Filter.eventually_of_forall (fun θ _ ↦ hpt _ (circleMap_mem_sphere 0 hr.le θ))
    · exact (IntervalIntegrable.const_mul hPi (ε / 2)).add intervalIntegrable_const
  have hint : ∫ θ in (0 : ℝ)..2 * π, (ε / 2 * poissonKernel 0 w (circleMap 0 r θ) + K) =
      ε / 2 * (2 * π) + K * (2 * π) := by
    rw [intervalIntegral.integral_add (IntervalIntegrable.const_mul hPi (ε / 2))
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, hPint, sub_zero, smul_eq_mul]
    ring
  have hfin : (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) = ε / 2 + K := by
    field_simp <;> ring
  rw [Real.dist_eq, poissonInt_sub hr hg hw (g ζ₀)]
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), ← Real.norm_eq_abs]
  calc _ ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π) + K * (2 * π)) :=
        mul_le_mul_of_nonneg_left (hbound.trans_eq hint) (by positivity)
    _ = ε / 2 + K := hfin
    _ < ε := by linarith
end ReciprocityTheory.AnForm.A
