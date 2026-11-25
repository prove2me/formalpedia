-- Prove2me | solution 1 for PI.PolynomialProperness.CA.finish_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:53.836458+00:00
-- url     : https://prove2.me/submissions/931d6b43-c1c7-4ba6-84df-985804771fa5

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
theorem _root_.solution {M C0 X A G : ℝ} (e : ℕ) (hm : M ≤ C0 * X ^ e) (hX : 0 ≤ X) (hXY : X ≤ A * G) :
    M ≤ max C0 0 * A ^ e * G ^ e := by
  calc M ≤ C0 * X ^ e := hm
    _ ≤ max C0 0 * X ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX e)
    _ ≤ max C0 0 * (A * G) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hXY e) (le_max_right _ _)
    _ = max C0 0 * A ^ e * G ^ e := by rw [mul_pow]; ring
end PI.PolynomialProperness.CA
