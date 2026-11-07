-- Prove2me | solution 1 for QEC.Locality.card_daiLiDGeKResidual_lt_of_separator_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:38.413198+00:00
-- url     : https://prove2.me/submissions/9bf9b971-c15b-4ad7-87e7-e80257debb05

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_card_daiLiDGeKResidual_le_separator

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
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell k : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell)
    (hSeparator : ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k) :
    ((daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card : ℝ) < k := by
  exact lt_of_le_of_lt (by
    exact_mod_cast card_daiLiDGeKResidual_le_separator P embedding d threshold w ell t
      hGlobal hw hEll) hSeparator
end QEC.Locality
