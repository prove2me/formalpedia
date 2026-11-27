-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projLineFlag_pushforward_hypotheses_adf4562d72f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:15:40.118776+00:00
-- url     : https://prove2.me/submissions/d53b2d23-d401-4d09-add7-8b3b01612355

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isPullHerm_pullHerm_924295e2684a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isQuotRows_noRows_069a8b58390d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothHerm_fubiniStudyO1_9e6fb0b9098d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_sqMetric


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
    flagDim 3 = 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧ IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) 0 3 ∧
    IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) (idRows 3) ∧ AllSmooth ![fsO1 2, fsO1 2] ∧
    (∀ j, IsPullHerm Sum.inl (inlV (ι := GlobalTheory 2) (ι₂ := PluckerBlocks 3 3)) (![fsO1 2, fsO1 2] j)
      (pullHerm isBlockMap_inl (![fsO1 2, fsO1 2] j))) ∧
    AllSmooth (fun _ : Fin (flagDim 3) => pluckerFubiniStudyO1) :=
  ⟨rfl, isArithVar_bot 1, isQuotRows_noRows 3, isKerBasis_idRows 3,
    fun j => by fin_cases j <;> exact isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _,
    fun _ => isSmoothHerm_sqMetric _⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
