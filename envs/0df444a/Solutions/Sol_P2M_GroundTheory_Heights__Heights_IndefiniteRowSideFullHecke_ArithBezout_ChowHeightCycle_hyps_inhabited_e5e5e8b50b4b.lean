-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowHeightCycle_hyps_inhabited_e5e5e8b50b4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:04.952111+00:00
-- url     : https://prove2.me/submissions/e03a7b1d-e80f-4683-8ebf-af8a6f966a98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_detForm_ne_zero_b96a0e200ace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_map_detForm_rat_c47efadec02b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
namespace ChowHeightCycle
theorem _root_.solution :
    (∀ w : NumberField.InfinitePlace ℚ, IsUnit ((fun _ => 1 : NumberField.InfinitePlace ℚ →
      Matrix (Fin 2) (Fin 2) ℂ) w)) ∧
      ∀ i ∈ (Finsupp.single (0 : Fin 1) 2).support, (fun _ => detForm ℚ) i ≠ 0 := by
  refine ⟨fun _ => isUnit_one, fun _ _ => ?_⟩
  intro h
  apply detForm_ne_zero
  rw [← map_detForm_rat]
  simp only at h
  rw [h, map_zero]
end ChowHeightCycle
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
