-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:43.621551+00:00
-- url     : https://prove2.me/submissions/0f304a79-83c6-4d02-9388-8410676080d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_const
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_mul


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {e : ℝ} {f : B.Mat k r → ℂ} (hf : PG e f) (m : ℕ) : PG ((m : ℝ) * e) (fun g => f g ^ m) := by
  induction m with
  | zero =>
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  | succ m ih =>
    have h := pb_mul ih hf
    have e1 : ((m + 1 : ℕ) : ℝ) * e = (m : ℝ) * e + e := by push_cast; ring
    rw [e1]
    convert h using 1
    funext g
    ring
end PI.UnitaryCorollaryDerivatives
