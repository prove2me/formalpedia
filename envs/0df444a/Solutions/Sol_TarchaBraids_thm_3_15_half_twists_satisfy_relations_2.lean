-- Prove2me | solution 2 for TarchaBraids.thm_3_15_half_twists_satisfy_relations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T13:40:16.096912+00:00
-- url     : https://prove2.me/submissions/67cc2bde-044a-482b-aba9-d9e1ffc078ea

import Mathlib
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_far_commute_v1
import Theorems.Thm_TarchaBraids_thm_3_15_half_twists_adjacent_braid_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ) :
    (∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
        halfTwistBraid n i * halfTwistBraid n j =
          halfTwistBraid n j * halfTwistBraid n i) ∧
    (∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
        halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
          halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j) := by
  exact ⟨TarchaBraids.thm_3_15_half_twists_far_commute_v1 n,
    TarchaBraids.thm_3_15_half_twists_adjacent_braid_v1 n⟩
