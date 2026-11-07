-- Prove2me | solution 1 for QEC.Locality.card_daiLiDGeKResidual_le_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:42.554417+00:00
-- url     : https://prove2.me/submissions/1c4ecf81-7918-40f1-be13-b26f3a110f56

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Locality_daiLiDGeKResidual_subset_separator

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
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell) :
    (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected.card ≤
      (daiLiDGeKSeparator P embedding threshold w ell t).card :=
  Finset.card_le_card
    (daiLiDGeKResidual_subset_separator P embedding d threshold w ell t hGlobal hw hEll)
end QEC.Locality
