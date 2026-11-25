-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.continuous_DjU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:37.89838+00:00
-- url     : https://prove2.me/submissions/0cf4cf1a-208a-4f1e-afae-1d79e4a5a009

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_continuous_vars
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_eval_qD


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
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution (k j ρ : ℕ) : Continuous (DjU k j ρ) := by
  have h : DjU k j ρ = fun g => eval (vars g) (qD k j ρ) := funext fun g => (eval_qD g).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp continuous_vars
end PI.UnitaryGroupMassFormula.UsCompose
