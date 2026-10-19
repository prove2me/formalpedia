-- Prove2me | solution 1 for SoficGroups.rankDrop_measureReal_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/dea0c157-d55b-428a-a451-5569abf30e8f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_measurableSet_shifted_floor_drop
import Theorems.Thm_SoficGroups_shifted_floor_drop_volume_bound_sharp

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (u v H : ℝ) (hH : 0 < H) (hvu : v ≤ u) :
    (MeasureTheory.volume.restrict (Set.Ico 0 H)).real
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
      u - v := by
  rw [MeasureTheory.measureReal_restrict_apply
    (measurableSet_shifted_floor_drop u v H)]
  have heq :
      {r : ℝ | ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ∩ Set.Ico 0 H =
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} := by
    ext r
    simp [and_comm]
  rw [heq, MeasureTheory.measureReal_def]
  have hbound := shifted_floor_drop_volume_bound_sharp u v H hH hvu
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (sub_nonneg.mpr hvu)] at hreal
end SoficGroups
