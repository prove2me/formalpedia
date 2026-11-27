-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.upper_block_rank_one_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:02.789801+00:00
-- url     : https://prove2.me/submissions/ac387a52-2b4f-41f6-8802-fdf28d4dfcea

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
theorem _root_.solution (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jF n ε * M.map c = jF n ε) :
    (M.toBlocks₁₁)ᵀ * (M.toBlocks₂₁).map c + (ε : R) • ((M.toBlocks₂₁)ᵀ * (M.toBlocks₁₁).map c) = 0 := by
  have hM' := hM
  rw [← fromBlocks_toBlocks M] at hM'
  simp only [jF, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_inj] at hM'
  have h := hM'.1
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, zero_add, add_zero] at h
  rw [add_comm]
  exact h
end PositivityTheory.SiegelWeilFormula.KAway
