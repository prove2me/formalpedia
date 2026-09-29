-- Prove2me | solution 1 for OddPerfectNumber.local_val_eq_of_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:28:59.776436+00:00
-- url     : https://prove2.me/submissions/472fda21-19a1-4b27-8fd3-c5f71b94125a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_lte_sub_one
import Theorems.Thm_OddPerfectNumber_local_sum_mod_self

open OddPerfectNumber

-- STAGED direct proof from proved imports: telescope, split valuations,
-- cancel. Hypothesis names kept clear of the concatenated-identifier
-- guard (hp/hp2/hq/hq1 sit in paren-free binders).
theorem solution (p q e : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq1 : p ∣ q - 1) :
    padicValNat p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)
      = padicValNat p (2 * e + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1lt : 1 < q := hq.one_lt
  have hq10 : q - 1 ≠ 0 := by omega
  have hS0 : (∑ i ∈ Finset.range (2 * e + 1), q ^ i) ≠ 0 := by
    intro hz
    have hmod := local_sum_mod_self q e hq
    rw [hz] at hmod
    simp at hmod
  have hS : (∑ i ∈ Finset.range (2 * e + 1), q ^ i) * (q - 1)
      = q ^ (2 * e + 1) - 1 :=
    geom_mul_sub_one q (2 * e + 1) hq1lt.le
  have hLTE : padicValNat p (q ^ (2 * e + 1) - 1)
      = padicValNat p (q - 1) + padicValNat p (2 * e + 1) :=
    lte_sub_one hp hp2 hq1lt hq1 (by omega)
  -- NOTE (remote CE d4b9aab6): ascribe the type so p is fixed before
  -- typeclass search for Fact p.Prime (see regression test).
  have hsplit : padicValNat p ((∑ i ∈ Finset.range (2 * e + 1), q ^ i) * (q - 1))
      = padicValNat p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)
        + padicValNat p (q - 1) :=
    padicValNat.mul hS0 hq10
  rw [hS] at hsplit
  omega
