-- Prove2me | solution 1 for QEC.Locality.exists_good_vertex_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:44:22.253583+00:00
-- url     : https://prove2.me/submissions/53ee1a5c-b3a1-45bd-8714-be9a856c1dad

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_vertexScore_eq_cast_count
import Theorems.Thm_QEC_Locality_integrable_vertexScore
import Theorems.Thm_QEC_Locality_average_vertexScore
import Theorems.Thm_QEC_Locality_volume_gridTranslation_ne_zero

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {a : Type*} [Fintype a] (w ell : ℝ) (hell : 0 < ell) (hscale : 4 * ell ≤ w)
    (X : a → ℝ × ℝ) :
    ∃ t : AddCircle w × AddCircle w,
      (vertexBadCount w (2 * ell) X t : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card a := by
  have hw : 0 < w := lt_of_lt_of_le (by nlinarith [hell]) hscale
  letI : Fact (0 < w) := ⟨hw⟩
  obtain ⟨t, ht⟩ := MeasureTheory.exists_le_average
    (volume_gridTranslation_ne_zero w) (integrable_vertexScore w (2 * ell) X)
  refine ⟨t, ?_⟩
  rw [← vertexScore_eq_cast_count]
  calc
    _ ≤ (⨍ s, vertexScore w (2 * ell) X s ∂volume) := ht
    _ = Fintype.card a * (16 * ell ^ 2 / w ^ 2) :=
      average_vertexScore w ell hell.le hscale X
    _ = 16 * (ell ^ 2 / w ^ 2) * Fintype.card a := by ring
    _ ≤ 32 * (ell ^ 2 / w ^ 2) * Fintype.card a := by gcongr <;> norm_num
    _ = (32 * ell ^ 2 / w ^ 2) * Fintype.card a := by ring
end QEC.Locality
