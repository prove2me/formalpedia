-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.selected_top_map2_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T05:05:01.494085+00:00
-- url     : https://prove2.me/submissions/d32fafaf-caaa-4278-b46f-e5217492ab0c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26OwnerParentObstruction_rzMap2_apply


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
theorem _root_.solution (S : OddScale) (word : Word3 S)
    (z : (state S 3).presentation.Z) (v : ZDoubleCylinderVertex (state S 3).presentation z S) :
    ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 word ⟨z,v⟩ =
      if v = rzMap1ZRoot (state S 3).presentation (state S 3).admissible z S
      then word z else 0 := by
  change map2Coord (state S 3).presentation (state S 3).admissible S word ⟨z,v⟩ = _
  exact BDL26OwnerParentObstruction.rzMap2_apply _ _ _ _ _ _
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
