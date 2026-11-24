-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure.pd_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:43.626153+00:00
-- url     : https://prove2.me/submissions/6381c14d-e5ca-4f9f-9419-de6e7094bde6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_const
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_mul

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N : ℕ}
namespace PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
theorem _root_.solution {a : ℕ} (c : ℂ) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : IsPolyDeg a P) :
    IsPolyDeg a (fun g => c * P g) := by
  have h := pd_mul (pd_const c) hP
  rwa [zero_add] at h
end PI.UnitaryCorollaryDerivatives.PolynomialDegreeClosure
