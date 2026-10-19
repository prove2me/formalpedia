-- Prove2me | solution 1 for SoficGroups.KunRealComplexMarkovBridge.indicatorVector_iterate_realMarkov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/d1dd1ce1-3f9d-4fc2-be4a-57f95dc4b638

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_indicatorVector_realMarkov

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRealComplexMarkovBridge
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    indicatorVector (((realMarkov p)^[k]) f) =
      ((permutationMarkov p)^[k]) (indicatorVector f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        indicatorVector_realMarkov, ih]
end SoficGroups.KunRealComplexMarkovBridge
