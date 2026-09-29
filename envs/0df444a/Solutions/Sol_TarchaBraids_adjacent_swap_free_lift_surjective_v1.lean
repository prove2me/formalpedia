-- Prove2me | solution 1 for TarchaBraids.adjacent_swap_free_lift_surjective_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T22:56:20.587579+00:00
-- url     : https://prove2.me/submissions/7664f6ae-0eb1-4fb2-a783-5118abd672f5

import Mathlib

theorem solution (m : ℕ) :
    Function.Surjective
      (FreeGroup.lift
        (fun i : Fin m =>
          (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (m + 1))))) := by
  rw [FreeGroup.lift_surjective_iff_closure_range_eq_top]
  exact
    Subgroup.closure_eq_top_of_mclosure_eq_top
      (Equiv.Perm.mclosure_swap_castSucc_succ m)
