-- Prove2me | solution 1 for PI.PolynomialProperness.real_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:19.77214+00:00
-- url     : https://prove2.me/submissions/d2ddce49-eea3-44d7-96a3-387ee4e99c77

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
theorem _root_.solution {C CA m n x : ℝ} {e : ℕ} (hm : 0 ≤ m) (hmx : m ≤ CA * x ^ e) (hx : 1 ≤ x)
    (hn : n ≤ C * m ^ 2) : n ≤ |C| * CA ^ 2 * x ^ (2 * e) := by
  have h1 : m ^ 2 ≤ (CA * x ^ e) ^ 2 := pow_le_pow_left₀ hm hmx 2
  have h2 : C * m ^ 2 ≤ |C| * m ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg m)
  calc n ≤ C * m ^ 2 := hn
    _ ≤ |C| * m ^ 2 := h2
    _ ≤ |C| * (CA * x ^ e) ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * CA ^ 2 * x ^ (2 * e) := by ring
end PI.PolynomialProperness
