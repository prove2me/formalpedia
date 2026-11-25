-- Prove2me | solution 1 for P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:15.007491+00:00
-- url     : https://prove2.me/submissions/4dbf8bd8-25f6-4ee2-bdc4-efe3cbd79661

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, X = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  obtain ⟨A', B', C', D', rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  have key : fromBlocks A B C D * fromBlocks (1 : Matrix m m K) B' 0 D' = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h12, h22]
    simp
  have := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at this
  simpa using this
end GlobalTheory
