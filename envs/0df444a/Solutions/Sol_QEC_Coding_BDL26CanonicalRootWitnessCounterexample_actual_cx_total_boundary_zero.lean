-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalRootWitnessCounterexample.actual_cx_total_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:30:36.858448+00:00
-- url     : https://prove2.me/submissions/2fec3b4c-8236-4a3c-a44f-2b3b256e7a02

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalRootWitnessCounterexample
import Theorems.Thm_QEC_Coding_BDL26CanonicalRootWitnessCounterexample_actual_cx_boundary_zero

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
    (hx : ∀ x, restrictWordLinear ((LX S).syndromeRegion x) sigma = 0) :
    d3 S (cxCorrectionTotal (A S) sigma) = 0 := by
  classical
  change d3 S (∑ x, cxComponentTotal (A S) sigma x) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun x _ => actual_cx_boundary_zero S sigma hx x)
end QEC.Coding.BDL26CanonicalRootWitnessCounterexample
