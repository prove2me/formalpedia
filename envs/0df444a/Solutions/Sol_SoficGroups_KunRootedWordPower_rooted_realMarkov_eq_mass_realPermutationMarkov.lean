-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.rooted_realMarkov_eq_mass_realPermutationMarkov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/9b62a459-a3c5-4289-aa9f-f7e95b1e9228

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) :
    SoficGroups.KunRealComplexMarkovBridge.realMarkov p =
      SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p := by
  funext f x
  simp [SoficGroups.KunRealComplexMarkovBridge.realMarkov,
    SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov,
    div_eq_mul_inv, mul_comm]
end SoficGroups.KunRootedWordPower
