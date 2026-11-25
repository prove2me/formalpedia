-- Prove2me | solution 1 for PI.PolynomialProperness.fmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:07.256923+00:00
-- url     : https://prove2.me/submissions/373112ca-0302-4351-b9bd-791af08ed232

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) :
    fmul k r z 1 b = fvec k r z b := by
  simp [fmul, Matrix.one_apply]
end PI.PolynomialProperness
