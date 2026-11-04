-- Prove2me | solution 1 for ThreeSum.PrimeChain.exists_contracting_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:13.194192+00:00
-- url     : https://prove2.me/submissions/bbd7220a-78a6-4359-8484-9a218f63d91c

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
    (weight : ℤ → ℕ) (C : Finset ℕ) (hC : C.Nonempty) (q K : ℕ)
    (havg : (∑ p ∈ C, score T difference weight (q * p)) ≤
      K * score T difference weight q) :
    ∃ p ∈ C, C.card * score T difference weight (q * p) ≤
      K * score T difference weight q := by
  obtain ⟨p, hp, hmin⟩ := C.exists_min_image (fun p => score T difference weight (q * p)) hC
  refine ⟨p, hp, le_trans ?_ havg⟩
  simpa [nsmul_eq_mul] using C.card_nsmul_le_sum
    (fun p => score T difference weight (q * p)) _ hmin
end ThreeSum.PrimeChain
