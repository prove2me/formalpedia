-- Prove2me | solution 1 for QEC.Locality.mem_daiLiDGeKGoodSide_into_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:15.485864+00:00
-- url     : https://prove2.me/submissions/5ecfa2af-20ce-4f01-825a-8fb787ede0d0

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_caseDGeKPieceFamily_union_selected


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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (side : DaiLiGridSideIndex)
    (hSide : side ∈ daiLiDGeKGoodBIndices embedding w t) (q : ι)
    (hq : q ∈ daiLiGridSideGoodQubits P embedding threshold w ell (gridOrigin w t) side) :
    q ∈ (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by
  rw [daiLiDGeKBSubsystem, caseDGeKPieceFamily_union_selected]
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨side, hSide, hq⟩
end QEC.Locality
