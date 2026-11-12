-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_X_query_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:36:28.307886+00:00
-- url     : https://prove2.me/submissions/8b6276c7-39eb-4743-96c0-370fc0c4c2e7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_G_restrict_X
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_val
import Theorems.Thm_QEC_Coding_BDL26IndexedDecoder_selectedMap_eq
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero

section
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
private theorem map2_X_query_zero (S : OddScale)
    (b : (CF S).Cochain2 (2 : LevelIndex 4))
    (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x)
      (((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b) = 0 := by
  ext p
  have hx : p.val ∈ (A S).xSector := by
    rw [(A S).xSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ x,p.property⟩
  have hz : p.val ∉ (A S).induced.zSector := by
    intro hp
    have hp' : p.val ∈ (A S).zSector := by
      rw [(A S).zSector_eq_induced]
      exact hp
    exact (Finset.disjoint_left.mp (A S).sectors_pairwise_disjoint.2.1) hx hp'
  change ((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b p.val = 0
  rw [selectedMap_eq]
  exact (A S).induced.map2_auxiliary_zero b p.val hz
open BDL26RXLocalReplacement BDL26RXStagedRestriction
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
end
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
end

set_option autoImplicit false
attribute [local irreducible] QEC.Coding.BDL26CanonicalHistoryMarks.rootComponent
open QEC QEC.Coding QEC.Coding.BDL26CanonicalRootWitnessCounterexample
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26ReplacementSupport
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical BigOperators
noncomputable section
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) (x : (state S 2).presentation.X) :
    restrictWordLinear ((LX S).syndromeRegion x) (lower3 S).val = 0 := by
  rw [lower3_val, map_add, map2_X_query_zero, zero_add]
  rw [(A S).contract.support_decomposition.cxDelta1_restriction_global,
    G_restrict_X, map_zero]
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
