-- Prove2me | solution 1 for ThreeSum.PrimeChain.modulus_score_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:23.20121+00:00
-- url     : https://prove2.me/submissions/39e772da-3570-4f11-8e61-1b5a8b32354c

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_ThreeSum_PrimeChain_exists_contracting_prime
import Theorems.Thm_ThreeSum_PrimeChain_selectPrime_min
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (candidates : List ℕ) (C : Finset ℕ)
    (hC : C.Nonempty) (hall : ∀ p ∈ C, p ∈ candidates)
    (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ) (K r : ℕ)
    (havg : ∀ q, (∑ p ∈ C, score T difference weight (q * p)) ≤
      K * score T difference weight q) :
    C.card ^ r * score T difference weight (modulus candidates T difference weight r) ≤
      K ^ r * score T difference weight 1 := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    let q := modulus candidates T difference weight r
    obtain ⟨p, hp, hcontract⟩ := exists_contracting_prime T difference weight C hC q K (havg q)
    have hselected := selectPrime_min candidates T difference weight q (hall p hp)
    have hstep : C.card * score T difference weight (q * selectPrime candidates T difference weight q) ≤
        K * score T difference weight q :=
      (Nat.mul_le_mul_left _ hselected).trans hcontract
    calc
      C.card ^ (r + 1) * score T difference weight (modulus candidates T difference weight (r + 1)) =
          C.card ^ r * (C.card * score T difference weight
            (q * selectPrime candidates T difference weight q)) := by simp only [modulus, q]; ring
      _ ≤ C.card ^ r * (K * score T difference weight q) := Nat.mul_le_mul_left _ hstep
      _ = K * (C.card ^ r * score T difference weight q) := by ring
      _ ≤ K * (K ^ r * score T difference weight 1) := Nat.mul_le_mul_left _ ih
      _ = K ^ (r + 1) * score T difference weight 1 := by ring
end ThreeSum.PrimeChain
