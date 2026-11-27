-- Prove2me | solution 1 for P2M_GlobalTheory_T_gram_det_ne_zero_of_ker_orth__c48c67bfcbef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:21.363875+00:00
-- url     : https://prove2.me/submissions/f7be44c7-1436-4042-9c43-e592ef5fd5dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrthStatement
import Theorems.Thm_GlobalTheory_gram_det_ne_zero_of_ker_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A) → (∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) → (∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) → (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  first | exact @GlobalTheory.gram_det_ne_zero_of_ker_orth | exact GlobalTheory.gram_det_ne_zero_of_ker_orth | (intros; apply GlobalTheory.gram_det_ne_zero_of_ker_orth <;> assumption)
end _root_.GlobalTheory.T
