-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_lamnorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:29.298857+00:00
-- url     : https://prove2.me/submissions/168396a1-a497-4611-b13d-040ef3e53d07

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
theorem _root_.solution (a b : ℕ) (c : ℂ) {j : ℕ} {m : ℝ} (hc : ‖c‖ ≤ (j : ℝ) * m) :
    ‖-((a : ℂ) * c + (b : ℂ) * conj c)‖ ≤ ((a + b : ℕ) : ℝ) * j * m := by
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_conj]
  push_cast
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hc hb]
end PI.UnitaryCorollaryDerivatives
