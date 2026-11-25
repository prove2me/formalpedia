-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteFibreCentredEquation_centredPoly_natDegree_lt_e101ed8c68bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:32:00.591446+00:00
-- url     : https://prove2.me/submissions/17d127b6-6c56-495a-bffb-0b33fdba0b78

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
theorem _root_.solution (a : ℂ) {k : ℕ} (c : Fin k → ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).natDegree < k + 1 := by
  refine Nat.lt_succ_of_le (natDegree_add_le_of_degree_le ?_ ?_)
  · rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
    exact j.isLt.le
end FiniteFibreCentredEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
