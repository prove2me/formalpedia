-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_ChowFormSectionPoint_hyps_inhabited_ff9bcb28a25b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:41.877931+00:00
-- url     : https://prove2.me/submissions/a314017e-0aef-417a-89ee-188bf2ee0110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isArithVar_point_a4ed8d13509c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_isChowForm_point_e29c8ba3cc02

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
namespace ChowFormSectionPoint
theorem _root_.solution :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) (0 + 1) ∧
      IsIntChowForm (⊥ : Ideal (MRing (PBlk 1))) 0 1 (X (0, 0)) ∧
        linForm (![1] : Fin 1 → ℤ) ∉ (⊥ : Ideal (MRing (PBlk 1))) := by
  classical
  refine ⟨isArithVar_point, ⟨fun c hc => ?_, by rw [map_X]; exact isChowForm_point⟩, ?_⟩
  · have h := hc (Finsupp.single (0, 0) 1)
    rw [coeff_X, if_pos rfl] at h
    exact isUnit_of_dvd_one h
  · rw [Submodule.mem_bot]
    simp [linForm, Xc, X_ne_zero]
end ChowFormSectionPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
