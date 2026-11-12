-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.top_owner_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:11:57.150205+00:00
-- url     : https://prove2.me/submissions/12ffbb46-0487-4468-b038-8571765e9e44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample

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
theorem _root_.solution (S : OddScale) (z : (state S 3).presentation.Z)
    (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    BDL26CanonicalHistoryMarks.syndromeOwner S 2 (1 : StepIndex 2)
      (⟨z,v⟩ : FamilyZ S 4 level4) = zVertex S 3 z := by rfl
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
