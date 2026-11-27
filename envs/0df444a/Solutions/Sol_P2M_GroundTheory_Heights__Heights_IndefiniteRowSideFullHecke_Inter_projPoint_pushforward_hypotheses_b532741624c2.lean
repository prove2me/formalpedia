-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projPoint_pushforward_hypotheses_b532741624c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:39.067527+00:00
-- url     : https://prove2.me/submissions/f19d6169-6d3e-4d43-83aa-782065e7e05f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isPullHerm_pullHerm_924295e2684a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_sq_c4df2bc29050
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_imageZ_blkV_bot_9dde23afa8cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isArithVar_bot_4411830e09a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSmoothHerm_fubiniStudyO1_9e6fb0b9098d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I4_isBlockMap_blkV


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
    IsBlockMap (blkOf 0) (blkV (Fin 2) 0) ∧ IsArithVar (⊥ : Ideal (MRing ProjLineSquareBlocks)) 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    (⊥ : Ideal (MRing (GlobalTheory 2))) ≤ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks)) ∧
    ringKrullDim (MRing (GlobalTheory 2) ⧸ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks))) <
      ((3 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    AllSmooth (fun _ : Fin 3 => fsO1 2) ∧
    ∀ _ : Fin 3, IsPullHerm (blkOf 0) (blkV (Fin 2) 0) (fsO1 2)
      (pullHerm (isBlockMap_blkV (Fin 2) 0) (fsO1 2)) := by
  refine ⟨isBlockMap_blkV (Fin 2) 0, isArithVar_bot_sq, isArithVar_bot 1, bot_le, ?_,
    fun _ => isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _⟩
  rw [imageZ_blkV_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  simp [Nat.card_eq_fintype_card]
  decide
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
