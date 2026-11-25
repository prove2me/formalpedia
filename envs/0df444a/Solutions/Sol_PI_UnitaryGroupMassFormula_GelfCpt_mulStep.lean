-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.mulStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:43.265436+00:00
-- url     : https://prove2.me/submissions/b56bb38f-100b-43bb-909f-3ce996d28e11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_IntegrableOfContinuousCpt
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_mul_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution : MulStep := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hc f₁ f₂ h₁ h₂
  ext i j
  simp only [intMat, Matrix.of_apply, Matrix.mul_apply]
  exact mul_entry μ (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
    (fun i j => hc.matrix_elem i j) (fun x y => by simp only [map_mul, Units.val_mul])
    f₁ f₂ h₁ h₂ i j
end PI.UnitaryGroupMassFormula.GelfCpt
