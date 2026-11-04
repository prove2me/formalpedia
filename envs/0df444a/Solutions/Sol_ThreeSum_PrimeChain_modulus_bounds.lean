-- Prove2me | solution 1 for ThreeSum.PrimeChain.modulus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:22.018613+00:00
-- url     : https://prove2.me/submissions/cd640161-5c39-4065-8521-89a3eea91e2e

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_ThreeSum_PrimeChain_selectPrime_mem
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (candidates : List ℕ) (hne : candidates ≠ [])
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (y Y r : ℕ)
    (hlo : ∀ p ∈ candidates, y ≤ p) (hhi : ∀ p ∈ candidates, p ≤ Y) :
    y ^ r ≤ modulus candidates T difference weight r ∧
      modulus candidates T difference weight r ≤ Y ^ r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hmem := selectPrime_mem candidates hne T difference weight
      (modulus candidates T difference weight r)
    constructor
    · simpa [modulus, pow_succ] using Nat.mul_le_mul ih.1 (hlo _ hmem)
    · simpa [modulus, pow_succ] using Nat.mul_le_mul ih.2 (hhi _ hmem)
end ThreeSum.PrimeChain
