-- Prove2me | solution 1 for QEC.Locality.daiLiKGeDRegionCore_subset_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:15:01.084696+00:00
-- url     : https://prove2.me/submissions/90b5956e-997a-480f-ac19-501cca60408d

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition

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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex) :
    daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region ⊆
      embedding.qubitsInRectangle
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).1
        (daiLiKGeDRegionRectangle embedding w (gridOrigin w t) rectangles region).2 := by
  exact Finset.filter_subset _ _
end QEC.Locality
