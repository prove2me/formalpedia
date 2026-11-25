-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:53.041137+00:00
-- url     : https://prove2.me/submissions/4aafe508-b400-48ca-aca1-ce827938c58b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurveRegularPoint

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NormalCurveRegularPoint
namespace GroundTheory.Heights₂.Heights.NormalCurveRegularPoint
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by
  induction g using MvPolynomial.induction_on generalizing z with
  | C a => simp
  | add p q hp hq =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hq' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) q z trivial).differentiableAt
    simp only [map_add]
    rw [fderiv_fun_add hp' hq']
    simp [hp, hq]
  | mul_X p j hp =>
    have hp' := (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) p z trivial).differentiableAt
    have hX : DifferentiableAt ℂ (fun x : σ → ℂ => x j) z := differentiableAt_apply j z
    simp only [eval_mul, eval_X]
    rw [fderiv_fun_mul hp' hX]
    simp [hp, Derivation.leibniz, pderiv_X, Pi.single_apply, fderiv_apply, mul_comm]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.NormalCurveRegularPoint
