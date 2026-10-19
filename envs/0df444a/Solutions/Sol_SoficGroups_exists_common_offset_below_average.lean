-- Prove2me | solution 1 for SoficGroups.exists_common_offset_below_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/9e4c8f74-6c88-4025-b9f7-efd52f7d83ec

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (H : ℝ) (hH : 0 < H) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f (Set.Ico 0 H)
      MeasureTheory.volume) :
    ∃ r ∈ Set.Ico 0 H,
      f r ≤ MeasureTheory.average
        (MeasureTheory.volume.restrict (Set.Ico 0 H)) f := by
  have hvolume : MeasureTheory.volume (Set.Ico (0 : ℝ) H) =
      ENNReal.ofReal H := by
    rw [Real.volume_Ico, sub_zero]
  have hnezero : MeasureTheory.volume (Set.Ico (0 : ℝ) H) ≠ 0 := by
    rw [hvolume]
    exact ENNReal.ofReal_ne_zero_iff.mpr hH
  have hnetop : MeasureTheory.volume (Set.Ico (0 : ℝ) H) ≠ ⊤ := by
    rw [hvolume]
    exact ENNReal.ofReal_ne_top
  exact MeasureTheory.exists_le_setAverage hnezero hnetop hf
end SoficGroups
