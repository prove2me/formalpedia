-- Prove2me | solution 1 for PI.PolynomialProperness.ut_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:51.923423+00:00
-- url     : https://prove2.me/submissions/1542349d-16eb-4b1e-b8f7-743836673f26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul

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
theorem _root_.solution {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v.det = 1 := by
  rw [Matrix.det_of_upperTriangular hv.1]
  simp [hv.2]
end PI.PolynomialProperness
