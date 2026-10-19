-- Prove2me | solution 1 for SoficGroups.integrable_rankDropIndicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/3114713b-c2a2-41a5-969e-d09e17c9b859

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
theorem _root_.solution
    (u v H : ℝ) :
    MeasureTheory.Integrable
      (fun r : ℝ =>
        if ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋ then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ico 0 H)) := by
  have hfinite : MeasureTheory.volume (Set.Ico (0 : ℝ) H) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hmeas : Measurable
      (fun r : ℝ =>
        if ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_shifted_floor_drop u v H)
      measurable_const measurable_const
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.restrict_of_bounded
    (1 : ℝ) hfinite
  filter_upwards [] with r
  split_ifs <;> norm_num
end SoficGroups
