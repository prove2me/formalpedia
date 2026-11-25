-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_analyticAt_eval_of_analyticAt_zero_79fc8297a2cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:46.652315+00:00
-- url     : https://prove2.me/submissions/e1e4fbb5-35a8-4997-a0a3-2c817b1b3d4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrdersLiftCentre

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
open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)
end GroundTheory.Heights₂.Heights
