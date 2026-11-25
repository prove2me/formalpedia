-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_YoungDiagramCombinatorics_card_monotone_equiv_congr_f5634ff25944
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:10.943413+00:00
-- url     : https://prove2.me/submissions/49e11591-5ba0-431f-966f-6539a14877c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
theorem _root_.solution {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)
    {n n' : ℕ} (h : n = n') :
    Nat.card {T : α ≃ Fin n // Monotone T} = Nat.card {T : β ≃ Fin n' // Monotone T} := by
  subst h
  exact Nat.card_congr
    { toFun := fun T => ⟨e.symm.toEquiv.trans T.1, fun a b hab => T.2 (e.symm.monotone hab)⟩
      invFun := fun T => ⟨e.toEquiv.trans T.1, fun a b hab => T.2 (e.monotone hab)⟩
      left_inv := fun T => by ext x; simp
      right_inv := fun T => by ext x; simp }
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
