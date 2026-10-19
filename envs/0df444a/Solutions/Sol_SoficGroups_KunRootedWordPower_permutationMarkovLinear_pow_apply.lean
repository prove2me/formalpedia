-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.permutationMarkovLinear_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/4865d26f-3f73-4b7e-8efc-ea85d3de3e5d

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
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (k : ℕ)
    (x : EuclideanSpace ℂ V) :
    ((permutationMarkovLinear p) ^ k) x =
      ((permutationMarkov p)^[k]) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply,
        Function.iterate_succ_apply']
      rw [ih, permutationMarkovLinear_apply]
end SoficGroups.KunRootedWordPower
