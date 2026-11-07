-- Prove2me | solution 1 for QEC.Locality.mem_daiLiKGeDGoodCellCore_into_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:22:03.441863+00:00
-- url     : https://prove2.me/submissions/8b09d799-97e5-418d-9eda-7764547442bc

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_into_A

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
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ)
    (hCandidate : Sum.inl cell ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell))
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : (gridCellLower w (gridOrigin w t) cell).1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < (gridCellUpper w (gridOrigin w t) cell).1 - ell ∧
        (gridCellLower w (gridOrigin w t) cell).2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < (gridCellUpper w (gridOrigin w t) cell).2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by
  apply mem_daiLiKGeDRegionCore_into_A P embedding d threshold w ell t cells rectangles
    (Sum.inl cell) hCandidate q
  change q ∈ (embedding.qubitsInRectangle
    (gridCellLower w (gridOrigin w t) cell) (gridCellUpper w (gridOrigin w t) cell)).filter
      (fun q =>
        q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles ∧
          (gridCellLower w (gridOrigin w t) cell).1 + ell < (embedding.point q).1 ∧
            (embedding.point q).1 < (gridCellUpper w (gridOrigin w t) cell).1 - ell ∧
              (gridCellLower w (gridOrigin w t) cell).2 + ell < (embedding.point q).2 ∧
                (embedding.point q).2 < (gridCellUpper w (gridOrigin w t) cell).2 - ell)
  exact Finset.mem_filter.mpr ⟨hRect, ⟨hNotSeparator, hStrict⟩⟩
end QEC.Locality
