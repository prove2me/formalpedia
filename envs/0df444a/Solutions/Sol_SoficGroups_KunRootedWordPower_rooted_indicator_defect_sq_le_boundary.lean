-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.rooted_indicator_defect_sq_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/ea156d79-a26e-4e2a-9f3f-22763732e019

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_realPermutationMarkov_indicator_defect_sq_le_boundary
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_permutationMarkov_indicator_sub_sq

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
    {ι V : Type*} [Fintype ι] [Nonempty ι]
    [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) :
    ‖permutationMarkov p
        (indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 ≤
      2 * (SoficGroups.boundary p T : ℝ) /
        (Fintype.card ι : ℝ) := by
  have hcomplex :
      SoficGroups.KunRealComplexMarkovBridge.permutationMarkov p =
        SoficGroups.KunRootedIndicatorCrossing.permutationMarkov p := rfl
  have hvector :
      SoficGroups.KunRealComplexMarkovBridge.indicatorVector
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T) =
        SoficGroups.KunRootedIndicatorCrossing.indicatorVector
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T) := rfl
  have hreal :
      SoficGroups.KunRealComplexMarkovBridge.realMarkov p
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T) =
        SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov p
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T) := rfl
  have henergy :=
    SoficGroups.KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
      p (SoficGroups.KunDirectedIndicatorJensen.realIndicator T)
  rw [hcomplex, hvector, hreal] at henergy
  have hindicator :
      SoficGroups.KunFinitePermutationMarkovMass.realIndicator T =
        SoficGroups.KunDirectedIndicatorJensen.realIndicator T := by
    funext x
    simp [SoficGroups.KunFinitePermutationMarkovMass.realIndicator,
      SoficGroups.KunDirectedIndicatorJensen.realIndicator]
  rw [hindicator]
  calc
    ‖permutationMarkov p
        (indicatorVector
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T)) -
        indicatorVector
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T)‖ ^ 2 =
      ∑ x,
        (SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov p
          (SoficGroups.KunDirectedIndicatorJensen.realIndicator T) x -
            SoficGroups.KunDirectedIndicatorJensen.realIndicator T x) ^ 2 := by
          exact henergy
    _ ≤ 2 * (SoficGroups.boundary p T : ℝ) /
        (Fintype.card ι : ℝ) :=
      SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
        p T
end SoficGroups.KunRootedWordPower
