-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_coeff_364200b5094e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.027966+00:00
-- url     : https://prove2.me/submissions/6da2761c-513b-4153-9e3f-0552a1dd7fab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteFibreCentredEquation
theorem _root_.solution (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (m : ℕ) :
    (FiniteFibreCentredEquation.centredPoly a c).coeff m =
      ((X - C a) ^ k).coeff m + ∑ j : Fin k, c j * ((X - C a) ^ (j : ℕ)).coeff m := by
  simp [FiniteFibreCentredEquation.centredPoly, finsetSum_coeff, coeff_C_mul]
end FiniteFibreCentredEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
