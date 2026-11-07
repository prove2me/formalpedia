-- Prove2me | solution 1 for QEC.Locality.daiLiBadGridTotalF_le_four_mul_globalCounter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:19:48.877218+00:00
-- url     : https://prove2.me/submissions/5e68741e-1ae7-4651-94cb-fe8460e75030

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Theorems.Thm_QEC_Locality_daiLiBadGridTotalF_le_daiLiGridClosedTotalF
import Theorems.Thm_QEC_Locality_daiLiGridClosedTotalF_le_four_mul_globalCounter
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
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : Nat)
    {w : ℝ} (hw : 0 < w) (origin : ℝ × ℝ) :
    daiLiBadGridTotalF P embedding threshold d w origin ≤
      4 * ∑ q : ι, P.daiLiInteractionCounter embedding threshold q := by
  exact (daiLiBadGridTotalF_le_daiLiGridClosedTotalF
    P embedding threshold d w origin).trans
      (daiLiGridClosedTotalF_le_four_mul_globalCounter P embedding threshold hw origin)
end QEC.Locality
