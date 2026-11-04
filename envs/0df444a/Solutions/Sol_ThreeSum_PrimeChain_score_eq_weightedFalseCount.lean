-- Prove2me | solution 1 for ThreeSum.PrimeChain.score_eq_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:09.63505+00:00
-- url     : https://prove2.me/submissions/63ff25c6-c99a-4ec8-a6a4-e403f4b71463

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
theorem _root_.solution (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (q : ℕ) :
    score T difference (Arithmetic.missWeight L) q =
      Arithmetic.weightedFalseCount T difference L (q : ℤ) := by
  simp only [score, Arithmetic.weightedFalseCount, Int.natCast_dvd]
end ThreeSum.PrimeChain
