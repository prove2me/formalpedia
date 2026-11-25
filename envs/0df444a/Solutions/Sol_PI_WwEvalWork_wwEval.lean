-- Prove2me | solution 1 for PI.WwEvalWork.wwEval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:51.294741+00:00
-- url     : https://prove2.me/submissions/5bba6df9-158a-4505-a49e-87422a755ee9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
import Theorems.Thm_PI_WwEvalWork_eval_applyAt0
import Theorems.Thm_PI_WwEvalWork_peval_Gxz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}
namespace PI.WwEvalWork
theorem _root_.solution : PI.WwEval.WwEval := by
  intro Lt _ _ l _ N0 N1 nu Th x I
  rw [eval_applyAt0, peval_Gxz]
  simp only [Lsum, wt, mul_assoc]
end PI.WwEvalWork
