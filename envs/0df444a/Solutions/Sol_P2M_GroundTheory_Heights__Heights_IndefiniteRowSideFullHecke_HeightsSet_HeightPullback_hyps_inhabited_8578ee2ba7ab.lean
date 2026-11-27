-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightPullback_hyps_inhabited_8578ee2ba7ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:55.932997+00:00
-- url     : https://prove2.me/submissions/f51653d9-47e7-474a-9d49-1f5d9608eea4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isArithVar_pointZ_46bf9e092250
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_mCoordIdeal_yPt_4a7603ebd995
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_id


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open NumberField
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
namespace HeightPullback
theorem _root_.solution :
    IsBlockMap (ι := PBlk 1) (ι' := PBlk 1) id id ∧ IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      IsArithVar (imageZ (ι := PBlk 1) (ι' := PBlk 1) id (mCoordIdeal yPt)) 1 ∧
      IsSmoothHerm (fsLine 1) ∧ IsPullHerm (ι := PBlk 1) (ι' := PBlk 1) id id (fsLine 1) (fsLine 1) ∧
      IntermediateField.relfinrank (blockFnField (yPt ∘ id)) (blockFnField yPt) = 1 := by
  have h1 : IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 := mCoordIdeal_yPt ▸ isArithVar_pointZ
  refine ⟨isBlockMap_id, h1, ?_, Inter.isSmoothHerm_fsLine 1, ⟨?_, fun _ ↦ rfl⟩,
    IntermediateField.relfinrank_self _⟩
  · have : imageZ (ι := PBlk 1) (ι' := PBlk 1) id (mCoordIdeal yPt) = mCoordIdeal yPt := by
      simp [imageZ, rename_id]
    rw [this]
    exact h1
  · funext k
    unfold pullDeg
    exact (Function.injective_id.extend_apply _ _ k).symm
end HeightPullback
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
