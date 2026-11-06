-- Prove2me | solution 1 for QEC.Locality.unitSeparated_card_in_thin_rectangle_le_six_mul_height
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:41:04.556205+00:00
-- url     : https://prove2.me/submissions/6aa95fca-be8a-4f85-8f55-995e71fa1504

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
    (embedding : UnitSeparatedEmbedding2D i) (s : Finset i)
    (lower upper : ℝ × ℝ)
    (hlong : 1 ≤ upper.2 - lower.2)
    (hthin0 : 0 ≤ upper.1 - lower.1) (hthin1 : upper.1 - lower.1 < 1)
    (hmem : ∀ p ∈ s, embedding.point p ∈ rectangle lower upper) :
    (s.card : ℝ) ≤ 6 * (upper.2 - lower.2) := by
  let swapped : UnitSeparatedEmbedding2D i :=
    { point := fun p => ((embedding.point p).2, (embedding.point p).1)
      unitSeparated := by
        intro p q hpq
        simpa [euclideanDistance2D, add_comm] using embedding.unitSeparated hpq }
  have hfour := unitSeparated_card_in_thin_rectangle_le_four_mul_longSide swapped s
    (lower.2, lower.1) (upper.2, upper.1) hlong hthin0 hthin1
    (by
      intro p hp
      have hpR := hmem p hp
      rcases hpR with ⟨⟨hplx, hpux⟩, ⟨hply, hpuy⟩⟩
      exact ⟨⟨hply, hpuy⟩, ⟨hplx, hpux⟩⟩)
  nlinarith
