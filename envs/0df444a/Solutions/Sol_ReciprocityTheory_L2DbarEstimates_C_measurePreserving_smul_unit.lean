-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.measurePreserving_smul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:30.604688+00:00
-- url     : https://prove2.me/submissions/1859d871-97af-49b7-bade-c1bfd808c433

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} (a : ℂ) (ha : ‖a‖ = 1) :
    MeasurePreserving (fun z : V n => a • z) volume volume := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let L : V n ≃ₗᵢ[ℝ] V n :=
    { toLinearEquiv := (LinearEquiv.smulOfNeZero ℂ (V n) a ha0).restrictScalars ℝ
      norm_map' := fun z => by simp [norm_smul, ha] }
  have hL : (fun z : V n => a • z) = L := by
    funext z
    rfl
  rw [hL]
  exact L.measurePreserving
end ReciprocityTheory.L2DbarEstimates.C
