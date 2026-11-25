-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatPosPartLocal_continuousOn_ratMap_76c7d0659315
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:00.503804+00:00
-- url     : https://prove2.me/submissions/162cedc1-d75d-4cbc-bf4d-5bda96ce343c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatPosPartLocal

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatPosPartLocal
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatPosPartLocal
theorem _root_.solution (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r => ((MvPolynomial.continuous_eval (p r)).continuousOn).div
    (MvPolynomial.continuous_eval q).continuousOn fun _ hx => hx
end GroundTheory.Heights₂.Heights.RatPosPartLocal
