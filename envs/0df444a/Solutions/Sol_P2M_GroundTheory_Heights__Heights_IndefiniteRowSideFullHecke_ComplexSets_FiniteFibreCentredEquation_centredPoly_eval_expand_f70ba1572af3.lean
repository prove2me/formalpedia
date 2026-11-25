-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_eval_expand_f70ba1572af3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:42.337088+00:00
-- url     : https://prove2.me/submissions/02fa0465-7c1b-446d-a46b-d411ecf4e158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteFibreCentredEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_coeff_top_145162f01264

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
theorem _root_.solution (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = T ^ k + ∑ m : Fin k, (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ (m : ℕ) := by
  rw [eval_eq_sum_range' (FiniteFibreCentredEquation.centredPoly_natDegree_lt a c), Finset.sum_range_succ, FiniteFibreCentredEquation.centredPoly_coeff_top,
    Finset.sum_range (fun m => (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ m)]
  ring
end FiniteFibreCentredEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
