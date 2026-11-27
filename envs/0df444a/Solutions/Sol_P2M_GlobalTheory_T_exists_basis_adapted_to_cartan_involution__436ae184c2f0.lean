-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_basis_adapted_to_cartan_involution__436ae184c2f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:51:42.072845+00:00
-- url     : https://prove2.me/submissions/b517ff8d-efad-4d44-a058-050fc4d5c1e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolutionStatement
import Theorems.Thm_GlobalTheory_exists_basis_adapted_to_cartan_involution


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef → ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧ Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧ s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by
  first | exact @GlobalTheory.exists_basis_adapted_to_cartan_involution | exact GlobalTheory.exists_basis_adapted_to_cartan_involution | (intros; apply GlobalTheory.exists_basis_adapted_to_cartan_involution <;> assumption)
end _root_.GlobalTheory.T
