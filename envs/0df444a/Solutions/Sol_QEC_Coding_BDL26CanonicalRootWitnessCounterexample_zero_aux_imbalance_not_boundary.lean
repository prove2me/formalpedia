-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.zero_aux_imbalance_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:42:19.225209+00:00
-- url     : https://prove2.me/submissions/af8cb1a9-5fa4-4521-a177-23a13f190d99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_zero_aux_valid_diagonal

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
theorem _root_.solution (S : OddScale) (sigma : Word3 S)
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0)
    (hq : ∀ q, restrictWordLinear ((LQ S).syndromeRegion q) sigma = 0)
    (z : (state S 2).presentation.Z)
    (hneq : sigma ((A S).induced.zPairEquiv (z,0)).val ≠
      sigma ((A S).induced.zPairEquiv (z,1)).val) :
    sigma ∉ LinearMap.range (d3 S) := by
  intro hvalid
  exact hneq (zero_aux_valid_diagonal S sigma hvalid hx hq z)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
