-- Prove2me | solution 1 for ThreeSum.PrimeChain.sum_scores_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:11.915346+00:00
-- url     : https://prove2.me/submissions/5407f6b0-2864-4576-9c05-48369e8a9b3b

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_WeightedCache3SUM_Alias_68cf541561a4a46d
import Definitions.Def_WeightedCache3SUM_Alias_cab4efaf9c64df13

set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q y M : ℕ) (hy : 1 < y)
    (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (hbound : ∀ i ∈ T, (difference i).natAbs ≤ M) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤
      Nat.log y M * score T difference weight q := by
  apply sum_scores_le T difference weight hzero C q (Nat.log y M)
  intro i hi hz
  exact (prime_divisors_card_le_log C y hy hprime hmin (difference i) hz).trans
    (Nat.log_mono_right (hbound i hi))
end ThreeSum.PrimeChain
