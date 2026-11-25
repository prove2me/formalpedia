-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_contDiff_eval_mvPolynomial_f33a1329f8bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:00.625852+00:00
-- url     : https://prove2.me/submissions/d71f7202-cbeb-4e0d-8e9f-2ffa68518488

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo

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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {ι : Type*} [Fintype ι] (q : MvPolynomial ι ℂ) :
    ContDiff ℂ 1 (fun y : ι → ℂ => MvPolynomial.eval y q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (contDiff_apply ℂ ℂ i)
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
