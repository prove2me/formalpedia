-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.rootMask_actual_nonzero_full_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:39:43.261869+00:00
-- url     : https://prove2.me/submissions/9f243846-ce41-4504-88ea-70e17cf3c176

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_gamma2_nonzero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_base_input
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_top_witness_not_boundary
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_rootMask_RZ_map2_failure

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
namespace QEC.Coding.BDL26CanonicalRootWitnessCounterexample
theorem _root_.solution (S : OddScale) :
    (BDL26CanonicalHistoryMarks.baseInput S 2 (upper4 S)).val ≠ 0 ∧
      topWitness S (upper4 S) ≠
        ((indexedDecoderData S 4).selectedMap (3 : StepIndex 4)).map2 (rootMaskMidWord S) ∧
      topWitness S (upper4 S) ∉ LinearMap.range ((CF S).coboundary1 level4) := by
  constructor
  · rw [actual_base_input]
    exact gamma2_nonzero S
  · exact ⟨rootMask_RZ_map2_failure S,actual_top_witness_not_boundary S⟩
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
