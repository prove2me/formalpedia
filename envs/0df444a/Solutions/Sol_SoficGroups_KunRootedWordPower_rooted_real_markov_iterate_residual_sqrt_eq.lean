-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.rooted_real_markov_iterate_residual_sqrt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/fe870aca-f841-4a9a-ac34-05fe3f7f85a5

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_iterate_permutationMarkov_indicator_sub_iterate_sq
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_realMarkov_eq_mass_realPermutationMarkov
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_final_realMarkov_eq_mass_realPermutationMarkov

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff
universe u
attribute [local instance] SoficGroups.KunRootedWordPower.rootedSparseModelDecidableEq
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    Real.sqrt
      (∑ x : V,
        (SoficGroups.KunActualFinalRestrictedVariation.realMarkov p
          ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T))) x -
          ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x)) ^ 2) =
      ‖((permutationMarkov p)^[k + 1])
          (indicatorVector
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        ((permutationMarkov p)^[k])
          (indicatorVector
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T))‖ := by
  have hcomplex :
      SoficGroups.KunRealComplexMarkovBridge.permutationMarkov p =
        SoficGroups.KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      SoficGroups.KunRealComplexMarkovBridge.indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) =
        SoficGroups.KunRootedIndicatorCrossing.indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) := rfl
  have henergy :=
    SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
      p (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T) k
  rw [hcomplex, hvector,
    rooted_realMarkov_eq_mass_realPermutationMarkov] at henergy
  have hfinal := rooted_final_realMarkov_eq_mass_realPermutationMarkov p
  have hsum :
      (∑ x : V,
        (SoficGroups.KunActualFinalRestrictedVariation.realMarkov p
          ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T))) x -
          ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x)) ^ 2) =
      ‖((permutationMarkov p)^[k + 1])
          (indicatorVector
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        ((permutationMarkov p)^[k])
          (indicatorVector
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T))‖ ^ 2 := by
    rw [hfinal]
    simpa only [Function.iterate_succ_apply'] using henergy.symm
  rw [hsum, Real.sqrt_sq (norm_nonneg _)]
end SoficGroups.KunRootedWordPower
