-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_heightOfCycle_hyp_4e3d46928265
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:39.035269+00:00
-- url     : https://prove2.me/submissions/1369b586-a840-4146-b881-6649a9689ad3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e

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
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    (X 0 + C 2 * X 1 : MvPolynomial (Fin 2) ℚ).map (algebraMap ℚ ℚ) =
      C 1 * ∏ _q : Fin 1, ∑ k, C (ratPointVec (Pi.basisFun (𝓞 ℚ) (Fin 2) k)) * X k := by
  simp [Fin.sum_univ_two, ratPointVec_apply]
end GroundTheory.Heights₂.Heights
