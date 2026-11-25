-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.eval_qDb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:20.27135+00:00
-- url     : https://prove2.me/submissions/ca606e5b-336a-467c-8dfc-e71a5fd5392d

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
theorem _root_.solution {k j ρ : ℕ} (g : Mat k (j + ρ)) : eval (vars g) (qDb k j ρ) = star (DjU k j ρ g) := by
  rw [qDb, DjU, RingHom.map_det, show star (Zh k j ρ g).det = (starRingEnd ℂ) (Zh k j ρ g).det from rfl,
    RingHom.map_det]
  congr 1
  ext a b
  simp [zPb, Zh, vars]
end PI.UnitaryGroupMassFormula.UsCompose
