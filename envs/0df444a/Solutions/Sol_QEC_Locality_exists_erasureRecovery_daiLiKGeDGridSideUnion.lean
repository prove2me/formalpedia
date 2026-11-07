-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiKGeDGridSideUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:21.652204+00:00
-- url     : https://prove2.me/submissions/ff39f8a2-b834-4066-ba02-9075218ee2e6

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiGridSideGoodFamily
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    {w ell : ℝ} (hEll : 0 < ell) (hWidth : 4 * ell ≤ w)
    (threshold : ℝ) (hThresholdEll : threshold ≤ ell)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles).erasureChannelFromRegister
        recovery := by
  obtain ⟨recovery, hRecovery⟩ := exists_erasureRecovery_daiLiGridSideGoodFamily
    P embedding d hDistance hEll hWidth threshold hThresholdEll (gridOrigin w t)
    (daiLiGridSideCandidates embedding w (gridOrigin w t)) hEdge hLong hSideSmall
  apply exists_erasureRecovery_of_finiteSubsystem_subset
    (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t cells rectangles)
    (familyUnionSubsystem (daiLiGridSideGoodFamily P embedding threshold w ell (gridOrigin w t))
      (daiLiGridSideCandidates embedding w (gridOrigin w t)))
  · intro q hq
    change q ∈ (daiLiGridSideCandidates embedding w (gridOrigin w t)).biUnion
      (fun side => (daiLiKGeDGridSideFamily P embedding threshold w ell t cells rectangles side).selected) at hq
    rcases Finset.mem_biUnion.mp hq with ⟨side, hside, hqSide⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨side, hside, ?_⟩
    change q ∈ daiLiGridSideGoodQubits P embedding threshold w ell (gridOrigin w t) side
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hqSide).1, ?_⟩
    intro hEndpoint
    exact (Finset.mem_sdiff.mp hqSide).2
      (Finset.mem_union_left _ (Finset.mem_union_right _ hEndpoint))
  · exact ⟨recovery, hRecovery⟩
end QEC.Locality
