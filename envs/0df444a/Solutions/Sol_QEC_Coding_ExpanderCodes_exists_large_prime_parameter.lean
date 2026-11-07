-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.exists_large_prime_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:09.301549+00:00
-- url     : https://prove2.me/submissions/16cdcc7c-81a5-4ed6-a59d-fcabd3503f50

import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_QEC_Coding_ExpanderCodes_PrimeFieldParameters
import Theorems.Thm_QEC_Coding_ExpanderCodes_exists_nonsquare_parameter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
namespace QEC.Coding.ExpanderCodes
theorem _root_.solution (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N ≤ p + 1 ∧ 3 ≤ p ∧
      ∃ epsilon : ZMod p, epsilon ≠ 0 ∧ ∀ r : ZMod p, r ^ 2 ≠ epsilon := by
  obtain ⟨p, hBound, hPrime⟩ := Nat.exists_infinite_primes (max N 3)
  have hN : N ≤ p := (le_max_left N 3).trans hBound
  have hThree : 3 ≤ p := (le_max_right N 3).trans hBound
  refine ⟨p, hPrime, by omega, hThree, ?_⟩
  letI : Fact p.Prime := ⟨hPrime⟩
  apply exists_nonsquare_parameter (ZMod p)
  rw [ZMod.ringChar_zmod_n]
  omega
end QEC.Coding.ExpanderCodes
