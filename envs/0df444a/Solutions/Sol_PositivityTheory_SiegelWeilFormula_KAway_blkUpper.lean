-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.blkUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:22.873382+00:00
-- url     : https://prove2.me/submissions/f22172ad-cace-4e0b-9f17-389043293a61

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution (A B D : Matrix (Fin n) (Fin n) R) (hM : (fromBlocks A B 0 D)ᵀ * jF n ε * (fromBlocks A B 0 D).map c = jF n ε) :
    Aᵀ * D.map c = 1 ∧ Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0 := by
  simp only [jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj] at hM
  obtain ⟨-, h12, -, h22⟩ := hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, zero_add,
    add_zero, transpose_zero, smul_zero] at h12 h22
  exact ⟨h12, by rw [add_comm]; exact h22⟩
end PositivityTheory.SiegelWeilFormula.KAway
