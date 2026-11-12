-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_Q_query
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:40:55.314672+00:00
-- url     : https://prove2.me/submissions/f809fa11-1201-46cc-8df9-8a911a88a2b4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actualQSection_spec
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_G_restrict_X
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_G_restrict_Q
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
private theorem map2_Q_query_zero (S : OddScale)
    (b : (CF S).Cochain2 (2 : LevelIndex 4))
    (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q)
      (((indexedDecoderData S 4).selectedMap (2 : StepIndex 4)).map2 b) = 0 := by
  ext p
  have hq : p.val ∈ (A S).qSector := by
    rw [(A S).qSector_eq_regions]
    exact Finset.mem_biUnion.mpr ⟨q,Finset.mem_univ q,p.property⟩
  have hz : p.val ∉ (A S).induced.zSector := by
    intro hp
    have hp' : p.val ∈ (A S).zSector := by
      rw [(A S).zSector_eq_induced]
      exact hp
    exact (Finset.disjoint_left.mp (A S).sectors_pairwise_disjoint.2.2) hq hp'
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
theorem _root_.solution (S : OddScale) (q : (state S 2).presentation.Q) :
    restrictWordLinear ((LQ S).syndromeRegion q) (lower3 S).val = localQuery S q := by
  rw [lower3_val, map_add, map2_Q_query_zero, zero_add]
  rw [(A S).contract.support_decomposition.cqDelta1_restriction_global q (G S)
    (G_restrict_X S), G_restrict_Q]
  exact (actualQSection_spec S q (localQuery S q) (localQuery_range S q)).1
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
