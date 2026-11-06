-- Prove2me | solution 2 for QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:17:43.643545+00:00
-- url     : https://prove2.me/submissions/7d522990-738a-4c03-9dcc-05adfa2d1af4

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_four_mul_longSide

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.1 - lower.1)
    (hthin0 : 0 ≤ upper.2 - lower.2) (hthin1 : upper.2 - lower.2 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.1 - lower.1) := by
  have hfour := unitSeparated_card_in_thin_rectangle_le_four_mul_longSide
    embedding s lower upper hlong hthin0 hthin1 hmem
  nlinarith
end QEC.Locality
