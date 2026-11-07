-- Prove2me | solution 1 for QEC.Locality.exists_daiLiDGeKSeparator_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:30:47.454162+00:00
-- url     : https://prove2.me/submissions/3acf104e-ef03-4c6b-a77e-26c14e2a9c67

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_card_daiLiDGeKSeparator_le_badCounts
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_exists_good_translation_for_qubits_and_longIncidences
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (hEll : 0 < ell) (hScale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) := by
  obtain ⟨t, hVertex, hEdge⟩ :=
    P.exists_good_translation_for_qubits_and_longIncidences embedding threshold w ell
      hEll hScale
  refine ⟨t, (card_daiLiDGeKSeparator_le_badCounts P embedding threshold w ell t).trans ?_⟩
  calc
    (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
          2 * (edgeBadCount w (2 * ell)
            (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          2 * ((16 * ell / w) *
            (2 * (P.longInteractionCount embedding threshold : ℝ))) := by
      gcongr
    _ = (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) := by
      ring
end QEC.Locality
