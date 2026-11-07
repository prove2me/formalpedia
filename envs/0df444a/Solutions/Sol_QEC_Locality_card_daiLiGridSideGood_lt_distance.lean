-- Prove2me | solution 1 for QEC.Locality.card_daiLiGridSideGood_lt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:19:17.441093+00:00
-- url     : https://prove2.me/submissions/68a743b6-7d3e-426a-bf8e-8a99845f42ba

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_card_daiLiGridSideStrip_le
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable
namespace QEC.Locality
theorem _root_.solution
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold : ℝ)
    {w ell : ℝ} (origin : ℝ × ℝ) (side : DaiLiGridSideIndex)
    (hEdge : 1 ≤ 2 * ell) (hLong : 1 ≤ w - 4 * ell)
    (hSmall : 12 * ell * (w - 4 * ell) < d) :
    (daiLiGridSideGoodQubits P embedding threshold w ell origin side).card < d := by
  have hLong' : 1 ≤ w - 2 * (2 * ell) := by linarith
  have hPacking := card_daiLiGridSideStrip_le embedding w ell (2 * ell) origin side
    hEdge hLong'
  have hPacking' :
      ((daiLiGridSideStripQubits embedding w ell (2 * ell) origin side).card : ℝ) ≤
        12 * ell * (w - 4 * ell) := by
    convert hPacking using 1 <;> ring
  have hSubset : daiLiGridSideGoodQubits P embedding threshold w ell origin side ⊆
      daiLiGridSideStripQubits embedding w ell (2 * ell) origin side :=
    Finset.sdiff_subset
  have hCard :
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side).card : ℝ) ≤
        ((daiLiGridSideStripQubits embedding w ell (2 * ell) origin side).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSubset
  have hCardReal :
      ((daiLiGridSideGoodQubits P embedding threshold w ell origin side).card : ℝ) < d :=
    lt_of_le_of_lt (hCard.trans hPacking') hSmall
  exact_mod_cast hCardReal
end QEC.Locality
