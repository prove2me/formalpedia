-- Prove2me | solution 1 for QEC.Locality.daiLiDGeKResidual_selected_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:14:07.749548+00:00
-- url     : https://prove2.me/submissions/5512167c-3659-4dbf-aac8-1941c4ae04c6

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
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected =
      Finset.univ \
        ((daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∪
          (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected) := rfl
end QEC.Locality
