-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.lower3_retained_imbalance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:57:51.378815+00:00
-- url     : https://prove2.me/submissions/7d660004-587e-4c6a-b6bd-0119f851f37c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_localW_at_q2_imbalance
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_lower3_retained_value

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
    (lower3 S).val ((A S).induced.zPairEquiv (r2 S,0)).val +
      (lower3 S).val ((A S).induced.zPairEquiv (r2 S,1)).val = 1 := by
  rw [lower3_retained_value,lower3_retained_value]
  calc
    (1 + _) + (1 + _) = ((1 : BDL26Field)+1) +
        (localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 0) +
          localW S (q2 S) (terminalVertex S (q2 S) (r2 S) (q2_incidence S) 1)) := by abel
    _ = 1 := by rw [ZModModule.add_self,localW_at_q2_imbalance,zero_add]
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
