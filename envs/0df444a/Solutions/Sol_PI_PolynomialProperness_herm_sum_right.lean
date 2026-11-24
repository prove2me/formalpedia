-- Prove2me | solution 1 for PI.PolynomialProperness.herm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:34:54.074901+00:00
-- url     : https://prove2.me/submissions/1b3d6e0d-ceb9-4867-be20-696bc29772aa

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
theorem _root_.solution {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ)
    (w : ι → ℂ) (y : ι → Fin n → ℂ) :
    herm H x (∑ d, w d • y d) = ∑ d, star (w d) * herm H x (y d) := by
  unfold herm
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [star_smul, smul_dotProduct, smul_eq_mul]
end PI.PolynomialProperness
