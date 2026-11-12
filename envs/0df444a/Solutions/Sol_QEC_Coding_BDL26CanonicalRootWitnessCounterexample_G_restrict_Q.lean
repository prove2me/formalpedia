-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.G_restrict_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:35:52.669317+00:00
-- url     : https://prove2.me/submissions/fa3947dc-c2d8-46d1-89b4-325c0dbd3854

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    restrictWordLinear ((LQ S).correctionRegion q) (G S) = localW S q := by
  classical
  ext p
  change (∑ r, extendWordLinear ((LQ S).correctionRegion r) (localW S r)) p.val = _
  rw [Finset.sum_apply]
  have hz (other : (state S 2).presentation.Q) (hne : other ≠ q) :
      extendWordLinear ((LQ S).correctionRegion other) (localW S other) p.val = 0 := by
    have hnot : p.val ∉ (LQ S).correctionRegion other := by
      intro ho
      exact (Finset.disjoint_left.mp
        ((A S).cq_correction_regions_pairwise_disjoint q other hne.symm)) p.property ho
    exact dif_neg hnot
  have hs := sum_single_value
    (fun r : (state S 2).presentation.Q =>
      extendWordLinear ((LQ S).correctionRegion r) (localW S r) p.val) q hz
  exact hs.trans (by exact dif_pos p.property)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
