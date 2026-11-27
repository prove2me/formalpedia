-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pfAI3_hyps_b91d1ed5823d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:48.620499+00:00
-- url     : https://prove2.me/submissions/a9f58a9b-baa8-46bc-97dc-e8f38b7dd6ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isPullHerm_pullHerm_924295e2684a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothHerm_fubiniStudyO1_9e6fb0b9098d
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution :
    IsBlockMap (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id id ∧ IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    imageZ (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id ⊥ = ⊥ ∧ IsChart (fibreIdeal id genFibreId) chartId ∧
    AllSmooth ![fsO1 2, fsO1 2] ∧
    ∀ j, IsPullHerm id id (![fsO1 2, fsO1 2] j) (pullHerm isBlockMap_id (![fsO1 2, fsO1 2] j)) :=
  ⟨isBlockMap_id, isArithVar_bot 1, imageZ_id_bot, fun k => (k.2 ⟨k.1, rfl⟩).elim,
    fun j => by fin_cases j <;> exact isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
