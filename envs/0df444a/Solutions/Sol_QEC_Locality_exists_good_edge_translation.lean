-- Prove2me | solution 1 for QEC.Locality.exists_good_edge_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:44:40.820333+00:00
-- url     : https://prove2.me/submissions/0379bba2-b8e1-429e-b78a-fd651351a2ae

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_edgeScore_eq_cast_count
import Theorems.Thm_QEC_Locality_integrable_edgeScore
import Theorems.Thm_QEC_Locality_average_edgeScore_le
import Theorems.Thm_QEC_Locality_volume_gridTranslation_ne_zero

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {b : Type*} [Fintype b] (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (Y : b → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (edgeBadCount w (2 * ell) Y t : ℝ) ≤
        (16 * ell / w) * Fintype.card b := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) (integrable_edgeScore w (2 * ell) Y)
  refine ⟨t, ?_⟩
  rw [← edgeScore_eq_cast_count]
  calc
    _ ≤ (⨍ s, edgeScore w (2 * ell) Y s ∂volume) := ht
    _ ≤ Fintype.card b * (8 * ell / w) :=
      average_edgeScore_le w ell hell.le hscale Y
    _ = 8 * (ell / w) * Fintype.card b := by ring
    _ ≤ 16 * (ell / w) * Fintype.card b := by gcongr <;> norm_num
    _ = (16 * ell / w) * Fintype.card b := by ring
end QEC.Locality
