-- Prove2me | solution 1 for QEC.Locality.mem_daiLiDGeKExceptional_into_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:10.051726+00:00
-- url     : https://prove2.me/submissions/0c6b1db0-4160-42c2-b478-ef64e4e88db6

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
    (t : GridTranslation w) (q : ι)
    (hq : q ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t) :
    q ∈ (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by
  rw [daiLiDGeKBSubsystem, caseDGeKPieceFamily_union_selected]
  exact Finset.mem_union_left _ hq
end QEC.Locality
