-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.sum_realPermutationMarkov_iterate_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/c199f26a-9a13-4365-ad20-e38e4e4d3d95

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_sum_realPermutationMarkov_iterate
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_sum_realIndicator

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution {V ι : Type*}
    [Fintype V] [DecidableEq V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    (∑ x : V,
      ((realPermutationMarkov σ)^[k]) (realIndicator T) x) =
        (T.card : ℝ) := by
  rw [sum_realPermutationMarkov_iterate]
  exact sum_realIndicator T
end SoficGroups.KunFinitePermutationMarkovMass
