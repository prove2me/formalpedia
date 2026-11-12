-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.eta_not_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:31:40.908201+00:00
-- url     : https://prove2.me/submissions/98f54d61-3410-4ab9-8442-d644715a4eda

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_zero_aux_imbalance_not_boundary
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_X_query_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_Q_query_zero
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_eta_retained_imbalance

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
theorem _root_.solution (S : OddScale) : eta S ∉ LinearMap.range (d3 S) := by
  apply zero_aux_imbalance_not_boundary S (eta S) (eta_X_query_zero S)
    (eta_Q_query_zero S) (r2 S)
  intro he
  have hi := eta_retained_imbalance S
  rw [he,ZModModule.add_self] at hi
  exact zero_ne_one hi
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
