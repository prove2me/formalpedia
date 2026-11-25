-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_contDiff_eval_pointOf_42c0fcab6353
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:25.542296+00:00
-- url     : https://prove2.me/submissions/1d0b4c3b-6ada-4122-8cec-cf5b0ce1f959

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ 1 (fun w => eval (h.pointOf w) q) := by
  have ha : AnalyticOnNhd ℂ (fun w => eval (h.pointOfC w) q) Set.univ :=
    (AnalyticOnNhd.eval_mvPolynomial q).comp (h.pointOfC.analyticOnNhd Set.univ)
      (fun _ _ => Set.mem_univ _)
  exact contDiffOn_univ.1 (ha.contDiffOn uniqueDiffOn_univ)
end GroundTheory.Heights₂.Heights
