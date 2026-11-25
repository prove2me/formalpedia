-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.differentiableAt_oneParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:51.642817+00:00
-- url     : https://prove2.me/submissions/d2a563fe-8990-440e-9e4b-efc503dbb969

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelCext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelDer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (φ : ℝ → (V →L[ℂ] V)) (hc : Continuous φ) (h0 : φ 0 = 1) (hadd : ∀ s t, φ (s + t) = φ s * φ t) :
    DifferentiableAt ℝ φ 0 := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set Φ : ℝ → (V →L[ℂ] V) := fun x => ∫ s in (0:ℝ)..x, φ s with hΦ
  have hΦd : ∀ x, HasDerivAt Φ (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Tendsto (slope Φ 0) (𝓝[≠] 0) (𝓝 (φ 0)) := hasDerivAt_iff_tendsto_slope.1 (hΦd 0)
  rw [h0] at hslope
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℝ), IsUnit (slope Φ 0 h) := hslope (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hh, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  rw [slope_def_module, hΦ0, sub_zero, sub_zero] at hh
  obtain ⟨u, hu⟩ := hh
  have key : ∀ t, φ t * Φ h = Φ (t + h) - Φ t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ (V →L[ℂ] V) (φ t)).intervalIntegral_comp_comm
      (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hΦ]
    dsimp only
    rw [← h1]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => φ x) t, add_zero,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hrep : φ = fun t => h⁻¹ • (Φ (t + h) - Φ t) * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) := by
    funext t
    rw [← key, ← mul_smul_comm, ← hu, Units.mul_inv_cancel_right]
  have hD : Differentiable ℝ Φ := fun x => (hΦd x).differentiableAt
  rw [hrep]
  exact ((((hD.comp (differentiable_id.add_const h)) 0).sub (hD 0)).const_smul h⁻¹).mul_const _
end ReciprocityTheory.ChartRestriction.DS.HW
