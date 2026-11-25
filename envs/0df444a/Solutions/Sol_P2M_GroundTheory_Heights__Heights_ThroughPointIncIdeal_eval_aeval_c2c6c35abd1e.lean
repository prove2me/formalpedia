-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:27.833965+00:00
-- url     : https://prove2.me/submissions/07936f08-cdf7-480b-87af-287016587090

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughPointIncIdeal

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
namespace GroundTheory.Heights₂.Heights
namespace ThroughPointIncIdeal
theorem _root_.solution {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end ThroughPointIncIdeal
end GroundTheory.Heights₂.Heights
