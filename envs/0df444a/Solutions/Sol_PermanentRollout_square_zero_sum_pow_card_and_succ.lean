-- Prove2me | solution 1 for PermanentRollout.square_zero_sum_pow_card_and_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/1f48e9fe-bd19-48ba-af68-960849b7794a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_square_zero_add_pow_succ

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (z : ι → R)
    (hz : ∀ i ∈ s, z i ^ 2 = 0) :
    ((∑ i ∈ s, z i) ^ s.card = (s.card.factorial : R) * ∏ i ∈ s, z i) ∧
      (∑ i ∈ s, z i) ^ (s.card + 1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hza : z a ^ 2 = 0 := hz a (by simp)
    have hzs : ∀ i ∈ s, z i ^ 2 = 0 := fun i hi => hz i (by simp [hi])
    obtain ⟨hcard, hnext⟩ := ih hzs
    constructor
    · rw [Finset.sum_insert ha, Finset.prod_insert ha,
        Finset.card_insert_of_notMem ha,
        square_zero_add_pow_succ hza hnext, hcard, Nat.factorial_succ, Nat.cast_mul]
      ring
    · rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have hnext' : (∑ i ∈ s, z i) ^ (s.card + 1 + 1) = 0 := by
        rw [pow_succ, hnext, zero_mul]
      simpa [hnext, Nat.add_assoc] using
        (square_zero_add_pow_succ (n := s.card + 1) hza hnext')
end PermanentRollout
