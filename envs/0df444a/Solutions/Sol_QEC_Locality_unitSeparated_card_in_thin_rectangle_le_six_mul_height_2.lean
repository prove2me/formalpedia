-- Prove2me | solution 2 for QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:17:55.512243+00:00
-- url     : https://prove2.me/submissions/678c03d8-944c-42d0-8be4-fd1cfc8a204c

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_four_mul_height

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {i : Type*} [DecidableEq i]
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.2 - lower.2) := by
  have hfour := unitSeparated_card_in_thin_rectangle_le_four_mul_height
    embedding s lower upper hlong hthin0 hthin1 hmem
  nlinarith
end QEC.Locality
