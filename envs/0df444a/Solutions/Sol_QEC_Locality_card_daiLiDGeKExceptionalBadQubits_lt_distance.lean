-- Prove2me | solution 1 for QEC.Locality.card_daiLiDGeKExceptionalBadQubits_lt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:06.016503+00:00
-- url     : https://prove2.me/submissions/343c641f-a9a4-451c-917f-40732fc8999e

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount
import Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_le_sum_counter


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
    (t : GridTranslation w) (d : ℕ)
    (hLongCount : 2 * P.longInteractionCount embedding threshold < d) :
    (daiLiDGeKExceptionalBadQubits P embedding threshold w ell t).card < d := by
  calc
    (daiLiDGeKExceptionalBadQubits P embedding threshold w ell t).card ≤
        (longInteractionEndpointQubits P embedding threshold).card :=
      Finset.card_le_card Finset.sdiff_subset
    _ ≤ ∑ q : ι, P.daiLiInteractionCounter embedding threshold q :=
      card_longInteractionEndpointQubits_le_sum_counter P embedding threshold
    _ = 2 * P.longInteractionCount embedding threshold :=
      P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding threshold
    _ < d := hLongCount
end QEC.Locality
