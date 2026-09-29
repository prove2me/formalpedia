-- Prove2me | solution 1 for TarchaBraids.braid_corrects_to_pure_range_of_quotient_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T08:23:43.018912+00:00
-- url     : https://prove2.me/submissions/c2ac6ab3-f4f9-41e7-8345-8dddc21545ef

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_halfTwist_deck_permutation_of_quotient_v1
import Theorems.Thm_TarchaBraids_strandIdx_swap_free_lift_surjective_v1
import Theorems.Thm_TarchaBraids_permutation_correction_to_kernel_v1
import Theorems.Thm_TarchaBraids_deck_kernel_eq_pure_range_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ)
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n)))
    (β : GeomBraidGroup n) :
    ∃ w : FreeGroup (Fin (n - 1)),
      β * (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w)⁻¹ ∈
        (FundamentalGroup.mapOfEq
          ⟨configProj n, hp.continuous⟩
          (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by
  obtain ⟨w, hw⟩ :=
    TarchaBraids.permutation_correction_to_kernel_v1 n hp
      (fun i => TarchaBraids.halfTwist_deck_permutation_of_quotient_v1 n i hp)
      (TarchaBraids.strandIdx_swap_free_lift_surjective_v1 n)
      β
  refine ⟨w, ?_⟩
  rw [← TarchaBraids.deck_kernel_eq_pure_range_v1 n hp]
  exact hw
