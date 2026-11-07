-- Prove2me | solution 1 for QEC.Locality.daiLiKGeD_partition_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:18:54.239379+00:00
-- url     : https://prove2.me/submissions/871664a4-6566-4ab2-aa3f-a55ae81bf839

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
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ))) :
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected ∧
    Disjoint (daiLiKGeDTrimmedBSubsystem P embedding d threshold w ell t cells rectangles).selected
      (daiLiKGeDResidualSubsystem P embedding d threshold w ell t cells rectangles).selected := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hB
    exact (Finset.mem_sdiff.mp hB).2 hA
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hA hC
    exact (Finset.mem_sdiff.mp hC).2 (Finset.mem_union_left _ hA)
  · apply Finset.disjoint_left.mpr
    intro q hB hC
    exact (Finset.mem_sdiff.mp hC).2 (Finset.mem_union_right _ hB)
end QEC.Locality
