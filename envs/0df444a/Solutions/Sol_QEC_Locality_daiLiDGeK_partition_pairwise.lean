-- Prove2me | solution 1 for QEC.Locality.daiLiDGeK_partition_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:17:24.951186+00:00
-- url     : https://prove2.me/submissions/00540fa1-65c1-402d-bb5e-094ce29c2a53

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition

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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected ∧
    Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ∧
    Disjoint (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected := by
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
