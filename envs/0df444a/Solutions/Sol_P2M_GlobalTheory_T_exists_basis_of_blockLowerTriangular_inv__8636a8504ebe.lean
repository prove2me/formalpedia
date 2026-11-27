-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_basis_of_blockLowerTriangular_inv__8636a8504ebe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:51:50.694125+00:00
-- url     : https://prove2.me/submissions/eabbe823-8201-49ef-a3b0-add1d8c0f749

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInvStatement
import Theorems.Thm_GlobalTheory_exists_basis_of_blockLowerTriangular_inv


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
theorem _root_.solution : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  first | exact @GlobalTheory.exists_basis_of_blockLowerTriangular_inv | exact GlobalTheory.exists_basis_of_blockLowerTriangular_inv | (intros; apply GlobalTheory.exists_basis_of_blockLowerTriangular_inv <;> assumption)
end _root_.GlobalTheory.T
