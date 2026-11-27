-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMinorsTrdeg_proof_86678097fe62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:31.302669+00:00
-- url     : https://prove2.me/submissions/58d49d31-a16f-4794-81a0-8f83e48e56e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_card_pivotIndex_9efc5db665c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace FlagMinorsTrdeg
theorem _root_.solution (h₁ : FlagPivotIdentity.Statement) (h₂ : FlagPivotAlgIndep.Statement) :
    FlagMinorsTrdeg.Statement := by
  intro F _ n
  have hx : AlgebraicIndependent F (pivotElt F n) :=
    AlgebraicIndependent.of_comp (flagMinorAlg F n).val (h₂ F n)
  have hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0 := fun a h =>
    hx.ne_zero ⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, le_rfl⟩⟩ (Subtype.ext h)
  have tb := hx.isTranscendenceBasis_iff_isAlgebraic.mpr (isAlgebraic_pivotAlg F n h₁ hne)
  have e := tb.cardinalMk_eq_trdeg
  rw [Cardinal.mk_fintype, card_pivotIndex] at e
  exact e.symm
end FlagMinorsTrdeg
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
