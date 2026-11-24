-- Prove2me | solution 1 for PI.PolynomialProperness.nsq_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:54.194261+00:00
-- url     : https://prove2.me/submissions/03c8b789-e6a6-460f-92e8-bb9f3b752863

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe

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
theorem _root_.solution {n : ℕ} (x : Fin n → ℂ) : nsq x = ∑ i, ‖x i‖ ^ 2 := by
  unfold nsq
  exact Finset.sum_congr rfl fun i _ => Complex.normSq_eq_norm_sq _
end PI.PolynomialProperness
