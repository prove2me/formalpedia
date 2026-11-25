-- Prove2me | solution 1 for PI.PolynomialProperness.CA.exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:46.934685+00:00
-- url     : https://prove2.me/submissions/5e5306a9-ee08-4cb1-a89e-a2f5e143d8b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInverseBoundOf

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
open PI PI.PolynomialProperness PI.PolynomialProperness.CA
namespace PI.PolynomialProperness.CA
theorem _root_.solution (r : ℕ) : (r + 1 - 1) * (r + 1) = r * (r + 1) := by
  rw [Nat.add_sub_cancel]
end PI.PolynomialProperness.CA
