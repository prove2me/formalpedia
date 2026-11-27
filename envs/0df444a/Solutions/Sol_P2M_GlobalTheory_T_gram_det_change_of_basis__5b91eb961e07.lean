-- Prove2me | solution 1 for P2M_GlobalTheory_T_gram_det_change_of_basis__5b91eb961e07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:11.233391+00:00
-- url     : https://prove2.me/submissions/4204d941-78dd-491f-9a13-9d043069b087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBases
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetChangeOfBasesStatement
import Theorems.Thm_GlobalTheory_gram_det_change_of_bases


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
theorem _root_.solution : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' → Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  first | exact @GlobalTheory.gram_det_change_of_bases | exact GlobalTheory.gram_det_change_of_bases | (intros; apply GlobalTheory.gram_det_change_of_bases <;> assumption)
end _root_.GlobalTheory.T
