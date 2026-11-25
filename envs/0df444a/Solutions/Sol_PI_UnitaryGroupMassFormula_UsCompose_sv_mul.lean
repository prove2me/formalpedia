-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.sv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:53.307834+00:00
-- url     : https://prove2.me/submissions/a9246d59-8d86-42b8-8db7-eaebd42ba5e5

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
theorem _root_.solution {k j ρ : ℕ} (s t : SC (2 * (j + ρ) + k + 1)) (g : Mat k (j + ρ)) :
    sv k j ρ (mulSC s t) g = sv k j ρ s g * sv k j ρ t g := by
  simp only [sv, mulSC, map_mul, pow_add]
  ring
end PI.UnitaryGroupMassFormula.UsCompose
