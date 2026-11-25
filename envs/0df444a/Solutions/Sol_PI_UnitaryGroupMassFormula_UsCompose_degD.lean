-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.degD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:12.916097+00:00
-- url     : https://prove2.me/submissions/e0424ea5-2c06-483a-8ec0-a6efba066ae7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution (k j ρ : ℕ) : (qD k j ρ).totalDegree ≤ j ∧ (qDb k j ρ).totalDegree ≤ j :=
  ⟨deg_det _ fun a b => by simp [zP, totalDegree_X], deg_det _ fun a b => by simp [zPb, totalDegree_X]⟩
end PI.UnitaryGroupMassFormula.UsCompose
