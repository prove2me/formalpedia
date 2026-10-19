-- Prove2me | solution 1 for SoficGroups.integrableOn_rankDropCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/ff11e10c-db4c-4b36-8910-f1bcca646dd3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_measurable_rankDropCount
import Theorems.Thm_SoficGroups_rankDropCount_nonneg_and_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H : ℝ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => rankDropCount u v H r)
      (Set.Ico 0 H) MeasureTheory.volume := by
  have hfinite : MeasureTheory.volume (Set.Ico (0 : ℝ) H) < ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  refine ⟨(measurable_rankDropCount u v H).aestronglyMeasurable, ?_⟩
  apply MeasureTheory.HasFiniteIntegral.restrict_of_bounded
    (Fintype.card ι : ℝ) hfinite
  filter_upwards [] with r
  rw [Real.norm_eq_abs, abs_of_nonneg
    (rankDropCount_nonneg_and_le u v H r).1]
  exact (rankDropCount_nonneg_and_le u v H r).2
end SoficGroups
