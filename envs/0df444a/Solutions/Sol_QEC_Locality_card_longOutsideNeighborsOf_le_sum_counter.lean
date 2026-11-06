-- Prove2me | solution 1 for QEC.Locality.card_longOutsideNeighborsOf_le_sum_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:41:43.378891+00:00
-- url     : https://prove2.me/submissions/d786352f-f953-4d70-b96e-51c144721f8e

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Theorems.Thm_QEC_Locality_card_longNeighborsOf_le_sum_counter

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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (region : Finset ι) :
    (longOutsideNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    (card_longNeighborsOf_le_sum_counter P embedding threshold region)
end QEC.Locality
