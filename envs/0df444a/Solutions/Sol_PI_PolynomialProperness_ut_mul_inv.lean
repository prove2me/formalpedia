-- Prove2me | solution 1 for PI.PolynomialProperness.ut_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:16.415524+00:00
-- url     : https://prove2.me/submissions/5ba1a5a6-4982-4131-985d-abff35211504

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul
import Theorems.Thm_PI_PolynomialProperness_ut_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (by rw [ut_det hv]; exact isUnit_one)
end PI.PolynomialProperness
