-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:38.365893+00:00
-- url     : https://prove2.me/submissions/771b2f81-bdd4-4daf-bfd3-dcd989ad4a32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong

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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution (Q : MvPolynomial (Fin N) ℂ) (p : Fin N → ℂ) :
    Measurable (polarIntegrand Q p) := by
  have hc : Continuous fun x : ℝ × (ℝ × (Fin N → ℂ)) =>
      ((x.2.1 : ℂ) * Complex.exp (x.1 * Complex.I)) • p + ((√(1 - x.2.1 ^ 2) : ℝ) : ℂ) • x.2.2 := by
    fun_prop
  exact Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval Q).comp hc)).measurable
end GroundTheory.Heights₂.Heights.PointwiseLelong
