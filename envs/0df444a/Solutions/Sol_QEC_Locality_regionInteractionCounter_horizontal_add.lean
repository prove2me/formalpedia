-- Prove2me | solution 1 for QEC.Locality.regionInteractionCounter_horizontal_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:19:17.638947+00:00
-- url     : https://prove2.me/submissions/6c8b174c-82f9-435e-b303-123afed9e627

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_horizontalRectangleQubits_disjoint
import Theorems.Thm_QEC_Locality_horizontalRectangleQubits_union

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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (lower upper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (lowerHorizontalRectangleQubits embedding lower upper cut) +
      regionInteractionCounter P embedding threshold
        (upperHorizontalRectangleQubits embedding lower upper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) := by
  classical
  unfold regionInteractionCounter
  rw [← Finset.sum_union
      (horizontalRectangleQubits_disjoint embedding lower upper cut),
    horizontalRectangleQubits_union]
end QEC.Locality
