-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.Bd.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:39:31.918657+00:00
-- url     : https://prove2.me/submissions/b5dd1e5b-46d8-4f07-9954-f6b2d9f48314

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
namespace Bd
theorem _root_.solution {k j ρ κ ℓ κ' ℓ' : ℕ} {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) (hκ : κ ≤ κ')
    (hℓ : ℓ ≤ ℓ') : Bd k j ρ κ' ℓ' L :=
  fun e he => ⟨(h e he).1.trans hκ, (h e he).2.1.trans hℓ, (h e he).2.2⟩
end Bd
end PI.UnitaryGroupMassFormula.UsCompose
