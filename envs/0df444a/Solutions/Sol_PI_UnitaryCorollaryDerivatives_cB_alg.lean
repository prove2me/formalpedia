-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:42.493657+00:00
-- url     : https://prove2.me/submissions/b7bcc0e9-78d7-48ec-a632-af6d5fe12b2a

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
theorem _root_.solution (a b : ℕ) (c D : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * c) * D)⁻¹ ^ a * (star (Complex.exp ((t : ℂ) * c) * D))⁻¹ ^ b =
      Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) * (D⁻¹ ^ a * (star D)⁻¹ ^ b) := by
  have e1 : star (Complex.exp ((t : ℂ) * c)) = Complex.exp ((t : ℂ) * conj c) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [star_mul', e1, mul_inv, mul_inv, mul_pow, mul_pow, ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) =
      Complex.exp ((a : ℂ) * -((t : ℂ) * c)) * Complex.exp ((b : ℂ) * -((t : ℂ) * conj c)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring
end PI.UnitaryCorollaryDerivatives
