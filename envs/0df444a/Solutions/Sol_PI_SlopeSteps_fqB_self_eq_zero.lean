-- Prove2me | solution 1 for PI.SlopeSteps.fqB_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:53.731244+00:00
-- url     : https://prove2.me/submissions/a7510e81-762a-4557-a7c6-56a893651b2e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Theorems.Thm_PI_SlopeSteps_fqB_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
variable {σ : Type}
namespace PI.SlopeSteps
theorem _root_.solution {c : ℚ} (hc : c ≠ 0) (P : MvPolynomial σ ℚ) (h : fqB c P P = 0) : P = 0 := by
  rw [fqB_apply, div_eq_zero_iff] at h
  by_contra hP
  exact (ne_of_gt ((fockQPos _ P P).2 hP)) (h.resolve_right hc)
end PI.SlopeSteps
