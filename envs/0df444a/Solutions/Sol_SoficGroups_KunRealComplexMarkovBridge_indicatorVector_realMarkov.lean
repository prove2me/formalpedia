-- Prove2me | solution 1 for SoficGroups.KunRealComplexMarkovBridge.indicatorVector_realMarkov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/3fec1303-6ddd-4ffa-b2cd-59fd73fa214d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRealComplexMarkovBridge
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    indicatorVector (realMarkov p f) =
      permutationMarkov p (indicatorVector f) := by
  ext x
  rw [indicatorVector_apply, permutationMarkov_apply]
  simp only [indicatorVector_apply]
  change (((∑ i, f ((p i).symm x)) /
    (Fintype.card ι : ℝ) : ℝ) : ℂ) =
      (∑ i, (f ((p i).symm x) : ℂ)) / (Fintype.card ι : ℂ)
  norm_cast
end SoficGroups.KunRealComplexMarkovBridge
