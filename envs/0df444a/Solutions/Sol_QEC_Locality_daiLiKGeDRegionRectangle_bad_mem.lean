-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDRegionRectangle_bad_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:14:08.918186+00:00
-- url     : https://prove2.me/submissions/a92e3c66-dc82-44d9-af03-d0383428b356

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiKGeDRegionRectangle_bad_eq_get

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length) :
    daiLiKGeDRegionRectangle embedding w origin rectangles (Sum.inr (cell, slot)) ∈
      rectangles cell := by
  rw [daiLiKGeDRegionRectangle_bad_eq_get embedding w origin rectangles cell slot hSlot]
  exact List.get_mem _ _
end QEC.Locality
