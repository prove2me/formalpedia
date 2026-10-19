-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.rooted_markov_real_iterate_sq_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/4cdf18c9-fe7d-4a1b-96bf-fcda534c2397

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_iterate_permutationMarkov_indicator_sub_sq
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_realMarkov_eq_mass_realPermutationMarkov

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 =
      ∑ x : V,
        ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x -
          if x ∈ T then (1 : ℝ) else 0) ^ 2 := by
  have h :=
    SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_sq
      p (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) k
  have hcomplex :
      SoficGroups.KunRealComplexMarkovBridge.permutationMarkov p =
        SoficGroups.KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      SoficGroups.KunRealComplexMarkovBridge.indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) =
        SoficGroups.KunRootedIndicatorCrossing.indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) := rfl
  rw [rooted_realMarkov_eq_mass_realPermutationMarkov] at h
  rw [hcomplex, hvector] at h
  simpa [SoficGroups.KunFinitePermutationMarkovMass.realIndicator] using h
end SoficGroups.KunRootedWordPower
