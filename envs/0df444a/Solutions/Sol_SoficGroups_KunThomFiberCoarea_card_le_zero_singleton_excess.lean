-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_le_zero_singleton_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/4d510931-843a-433e-9959-30ff601412ae

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V]
    (f : V → ℕ) :
    Fintype.card V ≤
      (Finset.univ.filter fun x : V => f x = 0).card +
        (singletonSupport f).card +
        ∑ x : V, (f x - 1 : ℕ) := by
  classical
  calc
    Fintype.card V = ∑ _ : V, (1 : ℕ) := by
      simp
    _ ≤ ∑ x : V,
          ((if f x = 0 then 1 else 0) +
            (if f x = 1 then 1 else 0) + (f x - 1)) := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hzero : f x = 0
          · simp [hzero]
          · by_cases hone : f x = 1
            · simp [hone]
            · simp [hzero, hone]
              omega
    _ = (Finset.univ.filter fun x : V => f x = 0).card +
          (singletonSupport f).card +
          ∑ x : V, (f x - 1 : ℕ) := by
          simp [Finset.sum_add_distrib, singletonSupport]
end SoficGroups.KunThomFiberCoarea
