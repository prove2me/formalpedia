-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_proof_d6fd7d5191ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:08.424041+00:00
-- url     : https://prove2.me/submissions/626c026f-f889-45e8-848c-1c7e001bc4fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughPointIncIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PThroughPointIncIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_aeval_c2c6c35abd1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ThroughPointIncIdeal_eval_genSubst_vanish_909cfb66c306

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
theorem _root_.solution : ThroughPointIncIdeal.Statement := by
  intro F _ n k Q x c hc hinc g hg
  apply MvPolynomial.funext
  intro a
  rw [map_zero, ThroughPointIncIdeal.eval_aeval]
  have hu := hinc (fun ij => eval a (genSubst (k := k) x c ij))
    (ThroughPointIncIdeal.eval_genSubst_vanish x c hc a)
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ hu
end ThroughPointIncIdeal
end GroundTheory.Heights₂.Heights
