-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ratDiv_eq_3319c2ebbdca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:50.280158+00:00
-- url     : https://prove2.me/submissions/0744f639-8a5b-4828-b686-7d4d9d22a798

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_divCycle_eq_e8d03d8e52b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.Targets.ProjContract
theorem _root_.solution (P : Ideal (NumbersDVR.MRing ι F)) (f g : NumbersDVR.MRing ι F)
    (W : Ideal (NumbersDVR.MRing ι F)) :
    NumbersDVR.ratDiv P f g W = AI.I1.ratDiv P f g W := by
  simp only [NumbersDVR.ratDiv, AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply]
  rw [Bridge.divCycle_eq, Bridge.divCycle_eq]
end GroundTheory.Heights₂.Heights.Targets.ProjContract
