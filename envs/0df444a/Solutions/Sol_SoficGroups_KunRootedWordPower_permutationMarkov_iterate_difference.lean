-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.permutationMarkov_iterate_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/e0957b2e-8f76-47cf-9329-65834ce9e357

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkovLinear_pow_apply

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (x : EuclideanSpace ℂ V)
    (k : ℕ) :
    ((permutationMarkov p)^[k + 1]) x -
        ((permutationMarkov p)^[k]) x =
      ((permutationMarkovLinear p) ^ k)
        (permutationMarkov p x - x) := by
  rw [Function.iterate_succ_apply]
  rw [← permutationMarkovLinear_pow_apply p k
    (permutationMarkov p x),
    ← permutationMarkovLinear_pow_apply p k x,
    ← map_sub]
end SoficGroups.KunRootedWordPower
