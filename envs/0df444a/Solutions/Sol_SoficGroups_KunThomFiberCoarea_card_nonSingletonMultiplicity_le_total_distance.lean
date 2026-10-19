-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonSingletonMultiplicity_le_total_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/7c0b1f98-d4a4-4fca-a0c3-42608d8bf44a

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
    (Finset.univ.filter fun x : V => f x ≠ 1).card ≤
      ∑ x : V, Nat.dist (f x) 1 := by
  classical
  calc
    (Finset.univ.filter fun x : V => f x ≠ 1).card =
        ∑ x : V, if f x ≠ 1 then 1 else 0 := by
          exact
            (Finset.sum_boole (R := ℕ)
              (fun x : V => f x ≠ 1) Finset.univ).symm
    _ ≤ ∑ x : V, Nat.dist (f x) 1 := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hx : f x = 1
          · simp [hx]
          · simp [hx, Nat.dist]
            omega
end SoficGroups.KunThomFiberCoarea
