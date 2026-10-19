-- Prove2me | solution 1 for SoficGroups.measurable_rankDropCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/bf198a88-1577-45d7-bc7b-6e687f035a35

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_measurableSet_shifted_floor_drop

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    Measurable (fun r : ℝ => rankDropCount u v H r) := by
  classical
  unfold rankDropCount
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite
    (measurableSet_shifted_floor_drop (u i) (v i) H)
    measurable_const measurable_const
end SoficGroups
