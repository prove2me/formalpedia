-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.G_boundary_at_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:47:35.812205+00:00
-- url     : https://prove2.me/submissions/3bfadc35-4174-446f-a36d-d2691acf8f1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_other_localW_boundary_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_q_boundary_at_terminal
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (S : OddScale) (b : Fin 2) :
    d3 S (G S) ((A S).induced.zPairEquiv (r2 S,b)).val =
      localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) b) := by
  classical
  rw [G,map_sum,Finset.sum_apply]
  have hz (q : (state S 2).presentation.Q) (hq : q ≠ q2 S) :
      d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q))
        ((A S).induced.zPairEquiv (r2 S,b)).val = 0 :=
    congrFun (other_localW_boundary_zero S q hq) _
  have hs := sum_single_value
    (fun q : (state S 2).presentation.Q =>
      d3 S (extendWordLinear ((LQ S).correctionRegion q) (localW S q))
        ((A S).induced.zPairEquiv (r2 S,b)).val) (q2 S) hz
  exact hs.trans (q_boundary_at_terminal S (q2 S) (localW S (q2 S))
    (r2 S) (q2_incidence S) b)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
