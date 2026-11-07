-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_daiLiKGeDB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:31:23.216265+00:00
-- url     : https://prove2.me/submissions/91c9a39a-2f1e-4687-a688-596c84a716b4

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDInternalSideFamily
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiKGeDGridSideUnion
import Theorems.Thm_QEC_Locality_daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled


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
    (threshold w ell : ℝ) (t : GridTranslation w)
    (atoms : (ℤ × ℤ) → List (ℝ × ℝ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (hAtoms : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding) ell
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).2 + w / 2) (atoms cell))
    (hRectangles : ∀ cell ∈ daiLiBadGridCells P embedding threshold d w (gridOrigin w t),
      rectangles cell = daiLiPhysicalGreedyRectangles P embedding threshold
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 - w / 2)
        ((daiLiGridCellCenter w (gridOrigin w t) cell).1 + w / 2) d (atoms cell))
    (hEllNat : 1 ≤ ell) (hCellWidth : 5 * ell ≤ w)
    (hInternalSideScale : 12 * ell * w < d)
    (hEll : 0 < ell) (hGridWidth : 4 * ell ≤ w)
    (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hGridLong : 1 ≤ w - 4 * ell)
    (hGridSideSmall : 12 * ell * (w - 4 * ell) < d) :
    ∃ recovery : QuantumChannel
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).complementSystem
        P.semanticCode
        (daiLiKGeDBSubsystem P embedding d threshold w ell t
          (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles).erasureChannelFromRegister
        recovery := by
  have hWidth : 0 < w := by nlinarith
  obtain ⟨gridRecovery, hGridRecovery⟩ := exists_erasureRecovery_daiLiKGeDGridSideUnion
    P embedding d hDistance hEll hGridWidth threshold hThresholdEll t
    (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles
    hEdge hGridLong hGridSideSmall
  obtain ⟨internalRecovery, hInternalRecovery⟩ :=
    exists_erasureRecovery_daiLiKGeDInternalSideFamily P embedding d hDistance threshold w ell t
      atoms rectangles hAtoms hRectangles hEllNat hCellWidth hInternalSideScale hEll hWidth
      hThresholdEll
  exact
    (exists_erasureRecovery_of_fixedGeneratorDecoupled P
      (daiLiKGeDGridSideUnionSubsystem P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      (daiLiKGeDInternalSideUnionSubsystem P embedding d threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) rectangles)
      gridRecovery internalRecovery hGridRecovery hInternalRecovery
      (daiLiKGeDGridSideUnion_fixedGeneratorDecoupled_internal P embedding d threshold w ell t
        atoms rectangles hAtoms hRectangles hEll hWidth hThresholdEll))
end QEC.Locality
