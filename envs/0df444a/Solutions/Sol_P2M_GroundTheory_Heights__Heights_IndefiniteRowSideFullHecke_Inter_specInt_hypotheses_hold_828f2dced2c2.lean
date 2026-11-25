-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_specInt_hypotheses_hold_828f2dced2c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:01.877988+00:00
-- url     : https://prove2.me/submissions/0277b4f1-d286-453b-9be6-83c869ad08b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothHerm_fubiniStudyO1_9e6fb0b9098d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_Xb_3b22cd5d65b8

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution : IsArithVar (⊥ : Ideal (MRing (GlobalTheory 1))) 1 ∧ IsSmoothHerm (fsO1 1) ∧
    IsSec (⊥ : Ideal (MRing (GlobalTheory 1))) (fsO1 1) (Xb 1 0) :=
  ⟨isArithVar_bot 0, isSmoothHerm_fubiniStudyO1 1, isSec_Xb 0 0⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
