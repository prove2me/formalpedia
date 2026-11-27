-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveNormalisationFinite_proof_426c6c224a49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:00:04.524836+00:00
-- url     : https://prove2.me/submissions/c24577fe-c8b2-4785-af5d-af3b88a8b336

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_eq_div_9ca7f60b5d9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_integralClosure_of_isReduced_6bb7a4513dbe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace CurveNormalisationFinite
theorem _root_.solution (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)
end CurveNormalisationFinite
end GroundTheory.Heights₂.Heights
