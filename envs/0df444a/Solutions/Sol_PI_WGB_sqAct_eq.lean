-- Prove2me | solution 1 for PI.WGB.sqAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:56.380768+00:00
-- url     : https://prove2.me/submissions/59144f28-515c-4fb7-8d8d-8ef1809eefde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Theorems.Thm_PI_WGB_detPow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g f = ((g : Matrix (Fin N) (Fin N) ℂ).det ^ lam.detShift) •
      rowAct ℂ (g : Matrix (Fin N) (Fin N) ℂ).transpose f := by
  rw [sqAct, detPow_eq]
end PI.WGB
