-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_ringEquiv_extending_of_ker_le__5ea22eb2e57f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:11.208239+00:00
-- url     : https://prove2.me/submissions/84faeafc-8346-4134-9f2c-6dc6437196d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLeStatement
import Theorems.Thm_GlobalTheory_exists_ringEquiv_extending_of_ker_le


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
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k], (∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) → ∀ (R : Subring k) (J : Type) (α β : J → k), (∀ p : MvPolynomial J R, MvPolynomial.aeval α p = 0 → MvPolynomial.aeval β p = 0) → ∃ φ : k ≃+* k, (∀ r ∈ R, φ r = r) ∧ ∀ j, φ (α j) = β j := by
  first | exact @GlobalTheory.exists_ringEquiv_extending_of_ker_le | exact GlobalTheory.exists_ringEquiv_extending_of_ker_le | (intros; apply GlobalTheory.exists_ringEquiv_extending_of_ker_le <;> assumption)
end _root_.GlobalTheory.T
