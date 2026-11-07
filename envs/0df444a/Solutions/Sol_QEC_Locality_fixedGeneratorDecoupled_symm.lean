-- Prove2me | solution 1 for QEC.Locality.fixedGeneratorDecoupled_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:07.355982+00:00
-- url     : https://prove2.me/submissions/5ea1f750-61a8-463a-91db-1ae475c388f7

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_symmetric


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
    {left right : Set ι}
    (h : P.fixedGeneratorDecoupled left right) :
    P.fixedGeneratorDecoupled right left := by
  refine ⟨h.1.symm, ?_⟩
  intro p hp q hq hInteraction
  exact h.2 hq hp (P.fixedGeneratorInteractionGraph_symmetric hInteraction)
end QEC.Locality
