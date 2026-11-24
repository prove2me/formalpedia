-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratPointVec_apply_6946ec36e89e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:39.89801+00:00
-- url     : https://prove2.me/submissions/2c86cfa8-a44d-405e-a021-eb4372874a7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw

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
theorem _root_.solution (x : Fin 2 → 𝓞 ℚ) : ratPointVec x = (x 0 : ℚ) + 2 * (x 1 : ℚ) := rfl
end GroundTheory.Heights₂.Heights
