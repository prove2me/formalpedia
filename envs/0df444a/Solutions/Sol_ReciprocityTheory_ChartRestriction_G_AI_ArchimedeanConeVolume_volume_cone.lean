-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.volume_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:45.686339+00:00
-- url     : https://prove2.me/submissions/2caa00de-a6a2-439a-a6d0-7c39dbb208ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_measurableSet_cone0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ArchimedeanConeVolume_volume_cone0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution {u : E3} (hu : ‖u‖ = 1) {s : Set ℝ} (hs : MeasurableSet s) :
    volume {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} =
      coneConst * volume (s ∩ Ioo (-1 : ℝ) 1) := by
  set e0 : E3 := EuclideanSpace.single 0 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  set L : E3 ≃ₗᵢ[ℝ] E3 := (ℝ ∙ (u - e0))ᗮ.reflection
  have hLu : L u = e0 := Submodule.reflection_sub (by rw [hu, he0])
  have hL0 : ∀ x : E3, (L x) 0 = inner ℝ x u := by
    intro x
    rw [← L.inner_map_map, hLu]
    simp [e0, EuclideanSpace.inner_single_right]
  have hset : {x : E3 | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ inner ℝ x u / ‖x‖ ∈ s} =
      L ⁻¹' {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, LinearIsometryEquiv.norm_map, hL0]
  rw [hset, L.measurePreserving.measure_preimage (measurableSet_cone0 hs).nullMeasurableSet,
    volume_cone0 hs]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
