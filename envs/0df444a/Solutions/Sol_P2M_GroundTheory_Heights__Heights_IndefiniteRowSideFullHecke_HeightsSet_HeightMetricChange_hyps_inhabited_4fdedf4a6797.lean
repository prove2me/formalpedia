-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_HeightMetricChange_hyps_inhabited_4fdedf4a6797
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:33.732826+00:00
-- url     : https://prove2.me/submissions/03d3f3b6-f336-46d3-b335-30f4c9b975b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_isArithVar_pointZ_46bf9e092250
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
namespace HeightMetricChange
theorem _root_.solution :
    IsSmoothHerm (fsLine 1) ∧ IsSmoothHerm fsLineScaled ∧ (fsLine 1).a = fsLineScaled.a ∧
      (∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 1))),
        |Real.log ((fsLine 1).h z / fsLineScaled.h z)| ≤ 1) ∧
      IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧ (⊥ : Ideal (MRing (PBlk 1))) ≤ ⊥ := by
  refine ⟨Inter.isSmoothHerm_fsLine 1, ?_, ?_, ?_, isArithVar_pointZ, le_rfl⟩
  · exact (Inter.isSmoothHerm_fsLine 1).mul contDiffOn_const
  · simp [fsLineScaled, HermLine.tensor, HermLine.ofWeight]
  · intro z hz
    have hpos := (fsLine 1).pos z hz.1
    simp only [fsLineScaled, HermLine.tensor, HermLine.ofWeight]
    rw [div_mul_cancel_left₀ hpos.ne', ← Real.exp_neg, neg_neg, Real.log_exp, abs_one]
end HeightMetricChange
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
