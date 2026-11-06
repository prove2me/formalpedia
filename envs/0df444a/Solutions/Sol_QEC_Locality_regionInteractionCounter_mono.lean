-- Prove2me | solution 1 for QEC.Locality.regionInteractionCounter_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:24.774968+00:00
-- url     : https://prove2.me/submissions/ac4676a9-87a8-4506-b9ca-dc9c6b4491d4

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
    {inner outer : Finset ι} (hSubset : inner ⊆ outer) :
    regionInteractionCounter P embedding threshold inner ≤
      regionInteractionCounter P embedding threshold outer := by
  unfold regionInteractionCounter
  exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun _ _ _ => Nat.zero_le _)
end QEC.Locality
