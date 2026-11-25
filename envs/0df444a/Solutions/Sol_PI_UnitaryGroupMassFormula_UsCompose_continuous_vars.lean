-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.continuous_vars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:37.627907+00:00
-- url     : https://prove2.me/submissions/dbb4eceb-1155-4780-b6c3-bd33e3e1218a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand

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
theorem _root_.solution {N : ℕ} : Continuous (vars : Matrix (Fin N) (Fin N) ℂ → Vr N → ℂ) := by
  refine continuous_pi fun i => ?_
  rcases i with x | x
  · exact (continuous_apply x.2).comp (continuous_apply x.1)
  · exact continuous_star.comp ((continuous_apply x.2).comp (continuous_apply x.1))
end PI.UnitaryGroupMassFormula.UsCompose
