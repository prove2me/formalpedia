-- Prove2me | solution 1 for SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/e413d5e8-22f0-4f7e-9c40-0a93b74e6f13

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_iterate_nonneg
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_iterate_le_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators
namespace SoficGroups.KunFinitePermutationMarkovMass
theorem _root_.solution
    {V ι : Type*}
    [DecidableEq V] [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) (x : V) :
    0 ≤ ((realPermutationMarkov σ)^[k]) (realIndicator T) x ∧
      ((realPermutationMarkov σ)^[k]) (realIndicator T) x ≤ 1 := by
  constructor
  · apply realPermutationMarkov_iterate_nonneg
    intro y
    by_cases hy : y ∈ T
    · simp [realIndicator, hy]
    · simp [realIndicator, hy]
  · apply realPermutationMarkov_iterate_le_one
    intro y
    by_cases hy : y ∈ T
    · simp [realIndicator, hy]
    · simp [realIndicator, hy]
end SoficGroups.KunFinitePermutationMarkovMass
