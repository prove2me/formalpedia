-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.mkTerm_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:34:53.189403+00:00
-- url     : https://prove2.me/submissions/1e4b2e26-2894-43c5-9739-aa8feabc8800

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ : ℕ} {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}
    (h : ∀ X ∈ e.2, inLie k (j + ρ) X) : (mkTerm (Wp := Wp) (Wq := Wq) k j ρ e).word = e.2 := by
  first
  | exact if_pos h
  | (show (if ∀ X ∈ e.2, inLie k (j + ρ) X then e.2 else []) = e.2; exact if_pos h)
  | (simp only [mkTerm]; exact if_pos h)
end PI.UnitaryGroupMassFormula.UsCompose
