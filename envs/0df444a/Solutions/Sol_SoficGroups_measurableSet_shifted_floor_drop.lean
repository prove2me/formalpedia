-- Prove2me | solution 1 for SoficGroups.measurableSet_shifted_floor_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/29da8e51-c970-461e-a26b-78ffa505921c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (u v H : ℝ) :
    MeasurableSet
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} := by
  have hv : Measurable (fun r : ℝ => ⌊(v + r) / H⌋) := by
    fun_prop
  have hu : Measurable (fun r : ℝ => ⌊(u + r) / H⌋) := by
    fun_prop
  exact measurableSet_lt hv hu
end SoficGroups
