-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_compatible_seq_of_finite_nonempty__5b0e872c7d40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:14.623285+00:00
-- url     : https://prove2.me/submissions/7758fb60-c092-423f-97a5-e13629fef834

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonempty
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonemptyStatement
import Theorems.Thm_GlobalTheory_exists_compatible_seq_of_finite_nonempty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n)), (∀ n, (Y n).Finite) → (∀ n, (Y n).Nonempty) → (∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) → ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  first | exact @GlobalTheory.exists_compatible_seq_of_finite_nonempty | exact GlobalTheory.exists_compatible_seq_of_finite_nonempty | (intros; apply GlobalTheory.exists_compatible_seq_of_finite_nonempty <;> assumption)
end _root_.GlobalTheory.T
