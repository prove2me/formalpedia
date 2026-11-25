-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_mx_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:32.567738+00:00
-- url     : https://prove2.me/submissions/a64c813b-e57d-435b-9075-6796a66af2bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {α : Type*} [Fintype α] {X : Matrix α α ℂ} (hX : ∀ a b, ‖X a b‖ ≤ 1) : mx X ≤ 1 := by
  unfold mx
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => hX a b
end PI.UnitaryCorollaryDerivatives
