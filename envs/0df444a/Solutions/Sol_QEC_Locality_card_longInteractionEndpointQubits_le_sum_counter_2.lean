-- Prove2me | solution 2 for QEC.Locality.card_longInteractionEndpointQubits_le_sum_counter
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:30:00.385612+00:00
-- url     : https://prove2.me/submissions/4513f75f-9602-4a3d-80fb-22fcf0156142

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

theorem solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) :
    (longInteractionEndpointQubits P embedding threshold).card ≤
      ∑ q, P.daiLiInteractionCounter embedding threshold q := by
  unfold longInteractionEndpointQubits
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro q _
  split_ifs with h
  · exact h
  · exact Nat.zero_le _
