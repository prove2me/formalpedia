-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.sum_indicator_nat_eq_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/4d626e42-2549-4911-8f2c-7cbf2366e9cf

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*}
    (A : Finset V) (q : V → Prop) [DecidablePred q] (m : ℕ) :
    (∑ x ∈ A, if q x then m else 0) =
      m * (A.filter q).card := by
  calc
    (∑ x ∈ A, if q x then m else 0) =
        m * (∑ x ∈ A, if q x then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = m * (A.filter q).card := by
          congr 1
          exact Finset.sum_boole (R := ℕ) q A
end SoficGroups.KunThomFiberCoarea
