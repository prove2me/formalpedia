-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:34.503113+00:00
-- url     : https://prove2.me/submissions/f4c0c62e-c5aa-478f-a424-aec1bcaf6971

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
theorem _root_.solution (Q : MvPolynomial (Fin N) ℂ) (v u : Fin N → ℂ) :
    Differentiable ℂ fun w : ℂ => eval (v + w • u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact differentiable_const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hp.mul (by fun_prop)
end GroundTheory.Heights₂.Heights.PointwiseLelong
