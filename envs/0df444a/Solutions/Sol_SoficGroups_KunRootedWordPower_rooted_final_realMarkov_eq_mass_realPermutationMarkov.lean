-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.rooted_final_realMarkov_eq_mass_realPermutationMarkov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/7939c83f-db8c-4ab8-aa59-bc65454b326c

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) :
    SoficGroups.KunActualFinalRestrictedVariation.realMarkov p =
      SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p := by
  funext f x
  simp [SoficGroups.KunActualFinalRestrictedVariation.realMarkov,
    SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov,
    div_eq_mul_inv, mul_comm]
end SoficGroups.KunRootedWordPower
