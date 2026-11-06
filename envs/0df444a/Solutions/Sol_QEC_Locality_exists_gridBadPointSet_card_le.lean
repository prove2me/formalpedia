-- Prove2me | solution 1 for QEC.Locality.exists_gridBadPointSet_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:18:58.485294+00:00
-- url     : https://prove2.me/submissions/bcdeae46-0ae9-4b4d-a4f9-7e6ada4f5341

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_card_gridBadPointSet_le_badCounts
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_exists_good_translation_for_qubits_and_longIncidences


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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (hell : 0 < ell) (hscale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          (32 * ell / w) * P.longInteractionCount embedding threshold := by
  obtain ⟨t, hvertex, hedge⟩ :=
    P.exists_good_translation_for_qubits_and_longIncidences
      embedding threshold w ell hell hscale
  refine ⟨t, (card_gridBadPointSet_le_badCounts
    P embedding threshold w ell t).trans ?_⟩
  calc
    _ ≤ (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
        (16 * ell / w) * (2 * P.longInteractionCount embedding threshold) :=
      add_le_add hvertex hedge
    _ = _ := by ring
end QEC.Locality
