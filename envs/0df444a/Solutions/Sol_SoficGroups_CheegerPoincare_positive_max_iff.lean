-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.positive_max_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/66013b5e-bd9e-4ad1-bf94-92d0e87f52f9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.CheegerPoincare
open scoped BigOperators
namespace SoficGroups.CheegerPoincare
theorem _root_.solution (a : ℝ) : 0 < max a 0 ↔ 0 < a := by
  by_cases ha : 0 < a
  · rw [max_eq_left ha.le]
  · rw [max_eq_right (le_of_not_gt ha)]
    simp [ha]
end SoficGroups.CheegerPoincare
