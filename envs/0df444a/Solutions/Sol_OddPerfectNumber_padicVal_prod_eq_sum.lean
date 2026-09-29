-- Prove2me | solution 1 for OddPerfectNumber.padicVal_prod_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:06:53.054859+00:00
-- url     : https://prove2.me/submissions/70487681-88b3-4b63-828f-939b44593caf

import Mathlib

-- STAGED direct proof: finset induction with padicValNat.mul.
-- Eliminator shape verified (Finset.induction_on, four explicit binders);
-- base case via eq_zero_of_not_dvd.
theorem solution (S : Finset ℕ) (f : ℕ → ℕ) (r : Nat)
    (hr : r.Prime) (hf : ∀ q ∈ S, f q ≠ 0) :
    padicValNat r (∏ q ∈ S, f q) = ∑ q ∈ S, padicValNat r (f q) := by
  haveI : Fact r.Prime := ⟨hr⟩
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact padicValNat.eq_zero_of_not_dvd (fun h => hr.ne_one (Nat.dvd_one.mp h))
  | insert a t ha ih =>
    intro hf
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a t)
    have hs : ∀ q ∈ t, f q ≠ 0 := fun q hq => hf q (Finset.mem_insert_of_mem hq)
    have hprod : (∏ q ∈ t, f q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValNat.mul hfa hprod, ih hs]
