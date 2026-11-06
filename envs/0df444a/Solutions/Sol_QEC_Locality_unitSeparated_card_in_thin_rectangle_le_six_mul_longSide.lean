-- Prove2me | solution 1 for QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_longSide
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:41:02.611661+00:00
-- url     : https://prove2.me/submissions/d0cca968-5ca9-4ab3-bec9-168ccc41198a

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_unitSeparated_card_in_thin_rectangle_le_four_mul_longSide

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable

theorem solution
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
