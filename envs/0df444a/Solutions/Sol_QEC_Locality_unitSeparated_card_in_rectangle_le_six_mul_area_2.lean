-- Prove2me | solution 2 for QEC.Locality.unitSeparated_card_in_rectangle_le_six_mul_area
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:43:26.500096+00:00
-- url     : https://prove2.me/submissions/4dd35872-ee3c-4ec3-9819-000a3e43efd2

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_packing_card_div_two_le_expanded_area
import Theorems.Thm_QEC_Locality_expanded_area_le_three_mul_area

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution
    {i : Type*} [DecidableEq i]
    (embedding : QEC.Locality.UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hwidth : 1 ≤ upper.1 - lower.1) (hheight : 1 ≤ upper.2 - lower.2)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * ((upper.1 - lower.1) * (upper.2 - lower.2)) := by
  have hpack := packing_card_div_two_le_expanded_area embedding s lower upper
    (by linarith) (by linarith) hmem
  have harea := expanded_area_le_three_mul_area hwidth hheight
  nlinarith
