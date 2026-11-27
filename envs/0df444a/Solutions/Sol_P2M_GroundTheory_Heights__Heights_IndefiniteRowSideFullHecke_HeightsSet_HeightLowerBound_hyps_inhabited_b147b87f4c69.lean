-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightLowerBound_hyps_inhabited_b147b87f4c69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:58:45.655599+00:00
-- url     : https://prove2.me/submissions/9302cc1a-2d50-46cf-8b1d-82bad2a33df1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isArithVar_pointZ_46bf9e092250
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_mCoordIdeal_yPt_4a7603ebd995
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isSectionBounded_one_0265e525520e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_noCommonZero_one_32569d64e5bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_one_mem_chartLat_7b9a2f66ac45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_fsLine_27a26231cd0b


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
namespace HeightLowerBound
theorem _root_.solution :
    IsSmoothHerm (fsLine 1) ∧ (∀ j, ![(1 : ℚ)] j ∈ chartLat yPt (fsLine 1).a 1) ∧
      (∀ j, IsSectionBounded (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1) (![(1 : ℚ)] j)
        (Real.exp 0)) ∧
      NoCommonZero (mCoordIdeal (ι := PBlk 1) yPt) yPt (fsLine 1).a ![(1 : ℚ)] ∧
      IsArithVar (mCoordIdeal (ι := PBlk 1) yPt) 1 ∧
      mCoordIdeal (ι := PBlk 1) yPt ≤ mCoordIdeal (ι := PBlk 1) yPt :=
  ⟨Inter.isSmoothHerm_fsLine 1, fun j ↦ by fin_cases j; exact one_mem_chartLat,
    fun j ↦ by fin_cases j; exact isSectionBounded_one, noCommonZero_one,
    mCoordIdeal_yPt ▸ isArithVar_pointZ, le_rfl⟩
end HeightLowerBound
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
