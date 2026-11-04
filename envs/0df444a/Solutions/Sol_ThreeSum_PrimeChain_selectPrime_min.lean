-- Prove2me | solution 1 for ThreeSum.PrimeChain.selectPrime_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:39.433196+00:00
-- url     : https://prove2.me/submissions/91c48459-f8c5-4b8f-a884-cbde0339293d

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
theorem _root_.solution (candidates : List ℕ) (T : Finset ι) (difference : ι → ℤ)
    (weight : ℤ → ℕ) (q : ℕ) {p : ℕ} (hp : p ∈ candidates) :
    score T difference weight (q * selectPrime candidates T difference weight q) ≤
      score T difference weight (q * p) := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => score T difference weight (q * p)) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some p =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := fun p => score T difference weight (q * p)) hp
      (by simpa only [Option.mem_def] using h)
end ThreeSum.PrimeChain
