-- Prove2me | solution 1 for ThreeSum.PrimeChain.sum_scores
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:11.933853+00:00
-- url     : https://prove2.me/submissions/df9ec341-6457-4ba5-ad93-03223d73f1e5

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (C : Finset ℕ) (q : ℕ) :
    (∑ p ∈ C, score T difference weight (q * p)) =
      ∑ i ∈ T, (C.filter fun p => q * p ∣ (difference i).natAbs).card *
        weight (difference i) := by
  unfold score
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  simp
end ThreeSum.PrimeChain
