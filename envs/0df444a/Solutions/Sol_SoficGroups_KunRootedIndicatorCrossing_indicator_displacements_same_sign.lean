-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.indicator_displacements_same_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/e4c1cc51-204a-417e-ac7d-adb55f3cfa5f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : V) :
    (∀ i, 0 ≤ f (p i x) - f x) ∨
      (∀ i, f (p i x) - f x ≤ 0) := by
  rcases hf x with hx | hx
  · left
    intro i
    rcases hf (p i x) with hi | hi <;> simp [hx, hi]
  · right
    intro i
    rcases hf (p i x) with hi | hi <;> simp [hx, hi]
end SoficGroups.KunRootedIndicatorCrossing
