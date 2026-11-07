-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiDGeKTrimmedB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:44.855197+00:00
-- url     : https://prove2.me/submissions/4a22309e-1233-4314-9bd6-b96054ceab3a

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKB
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_finiteSubsystem_subset


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
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hLongStrip : 1 ≤ w - 4 * ell)
    (hSmallStrip : 12 * ell * (w - 4 * ell) < d)
    (hLongCount : 2 * P.longInteractionCount embedding threshold < d) :
    ∃ recovery : QuantumChannel
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).complementSystem
        P.semanticCode
        (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).erasureChannelFromRegister
        recovery := by
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t)
    (daiLiDGeKBSubsystem P embedding threshold w ell t)
  · exact Finset.sdiff_subset
  · exact exists_erasureRecovery_daiLiDGeKB P embedding d hDistance threshold w ell t
      hEll hWidth hThresholdEll hEdge hLongStrip hSmallStrip hLongCount
end QEC.Locality
