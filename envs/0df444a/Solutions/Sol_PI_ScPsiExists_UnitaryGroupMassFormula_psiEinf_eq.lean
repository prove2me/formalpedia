-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:34.507416+00:00
-- url     : https://prove2.me/submissions/ae0ca33f-9bc9-4c13-92eb-a36fa29ffb88

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_sHom_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (I : AutInst) (x : I.E) :
    psiEinf I x = Complex.exp (2 * Real.pi * Complex.I * ((sHom I x : ℝ) : ℂ)) := by
  rw [sHom_coe, Finset.mul_sum, Complex.exp_sum]
  rfl
end PI.ScPsiExists.UnitaryGroupMassFormula
