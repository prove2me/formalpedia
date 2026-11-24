-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.eval_qD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:11.715853+00:00
-- url     : https://prove2.me/submissions/63947410-109b-44ca-9407-f837ac7a4a0c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow

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
theorem _root_.solution {k j ρ : ℕ} (g : Mat k (j + ρ)) : eval (vars g) (qD k j ρ) = DjU k j ρ g := by
  rw [qD, DjU, RingHom.map_det]
  congr 1
  ext a b
  simp [zP, Zh, vars]
end PI.UnitaryGroupMassFormula.UsCompose
