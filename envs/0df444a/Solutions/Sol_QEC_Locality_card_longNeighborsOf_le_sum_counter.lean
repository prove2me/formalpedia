-- Prove2me | solution 1 for QEC.Locality.card_longNeighborsOf_le_sum_counter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:32.512348+00:00
-- url     : https://prove2.me/submissions/9fe0ac47-454e-4227-b227-bf880cb8866e

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition

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
    (longNeighborsOf P embedding threshold region).card ≤
      ∑ q ∈ region, P.daiLiInteractionCounter embedding threshold q := by
  classical
  calc
    _ ≤ ∑ q ∈ region,
        ((P.longInteractionGraph embedding threshold).neighborFinset q).card :=
      Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [daiLiInteractionCounter, ← SimpleGraph.card_neighborFinset_eq_degree]
end QEC.Locality
