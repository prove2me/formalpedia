-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.RootedIndicatorMarkovModel.IsRootedAtRadius.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/f040f8ec-4f45-4e29-8fab-23bc8c9a6b6c

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
universe u v
namespace SoficGroups.KunRootedWordPower
namespace RootedIndicatorMarkovModel.IsRootedAtRadius
theorem _root_.solution
    {G ι : Type u} [Group G]
    {X : RootedIndicatorMarkovModel G ι}
    {w : G → List ι} {r R : ℕ}
    (h : X.IsRootedAtRadius w R) (hr : r ≤ R) :
    X.IsRootedAtRadius w r :=
  ⟨fun a g hword => h.out a g (hword.trans hr)⟩
end RootedIndicatorMarkovModel.IsRootedAtRadius
end SoficGroups.KunRootedWordPower
