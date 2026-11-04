-- Prove2me | solution 1 for ThreeSum.PrimeChain.selectPrime_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:38.180258+00:00
-- url     : https://prove2.me/submissions/7c970f41-e57a-40a3-8430-f72ab441eb4e

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
theorem _root_.solution (candidates : List ℕ) (hne : candidates ≠ [])
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (q : ℕ) :
    selectPrime candidates T difference weight q ∈ candidates := by
  unfold selectPrime
  cases h : candidates.argmin (fun p => score T difference weight (q * p)) with
  | none => exact False.elim (hne (List.argmin_eq_none.mp h))
  | some p =>
    simp only [Option.getD_some]
    exact List.argmin_mem (f := fun p => score T difference weight (q * p))
      (by simpa only [Option.mem_def] using h)
end ThreeSum.PrimeChain
