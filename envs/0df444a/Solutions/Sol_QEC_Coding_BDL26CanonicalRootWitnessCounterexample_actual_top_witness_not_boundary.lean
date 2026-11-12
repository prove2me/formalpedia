-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_top_witness_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:37:53.098199+00:00
-- url     : https://prove2.me/submissions/c59d7646-18d3-401e-9c8f-ed64e659a453

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_top_RZ_reflects_boundary
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_topWitness_factor
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_not_boundary

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
open BDL26RXLocalReplacement BDL26RXStagedRestriction
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    topWitness S (upper4 S) ∉
      LinearMap.range ((CF S).coboundary1 level4) := by
  intro h
  rw [topWitness_factor] at h
  exact eta_not_boundary S (top_RZ_reflects_boundary S (eta S) h)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
