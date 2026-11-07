-- Prove2me | solution 1 for QEC.Locality.no_fixedGeneratorInteraction_from_outside_longEndpoints_of_threshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:04:01.703536+00:00
-- url     : https://prove2.me/submissions/ef270da6-0c1e-4509-81ea-e6b1c4a8be69

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_fixedGeneratorInteractionGraph_loopless
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_one_le_distance_of_ne
import Theorems.Thm_QEC_Locality_no_long_interaction_from_outside_endpoint_set


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {threshold : ℝ}
    (hThreshold : threshold < 1) {p q : ι}
    (hp : p ∉ longInteractionEndpointQubits P embedding threshold)
    (hInteraction : P.fixedGeneratorInteraction p q) : False := by
  apply no_long_interaction_from_outside_endpoint_set P embedding threshold p q hp
  refine ⟨hInteraction, hThreshold.le.trans ?_⟩
  apply embedding.one_le_distance_of_ne
  intro hpq
  subst q
  exact P.fixedGeneratorInteractionGraph_loopless p hInteraction
end QEC.Locality
