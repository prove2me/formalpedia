-- Prove2me | solution 1 for PI.PolynomialProperness.CoreW.final_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:42:22.132813+00:00
-- url     : https://prove2.me/submissions/62b6bd83-56e1-4d79-a07a-1036688a2f20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_IsoRightInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
open PI.PolynomialProperness.CoreW
variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.PolynomialProperness.CoreW
theorem _root_.solution (D R0 E K c X a b : ℝ) (hD0 : 0 ≤ D) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hc : c = 1 + D * K) (ha : a ≤ D ^ 2 * R0 ^ 2 * K * X) (hb : b ≤ c * (E ^ 2 * X)) :
    2 * a + 2 * b ≤ (2 * D ^ 2 * R0 ^ 2 + 2 * (1 + D) * E ^ 2) * (1 + K) ^ 2 * X := by
  subst hc
  have h1 : D ^ 2 * R0 ^ 2 * K * X ≤ D ^ 2 * R0 ^ 2 * (1 + K) ^ 2 * X := by
    have hk : K ≤ (1 + K) ^ 2 := by nlinarith
    have hp : 0 ≤ D ^ 2 * R0 ^ 2 * X := mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg R0)) hX
    nlinarith
  have h2 : (1 + D * K) * (E ^ 2 * X) ≤ (1 + D) * E ^ 2 * (1 + K) ^ 2 * X := by
    have hk : 1 + D * K ≤ (1 + D) * (1 + K) ^ 2 := by
      nlinarith [mul_nonneg hD0 hK, sq_nonneg K, mul_nonneg hD0 (sq_nonneg K)]
    have hp : 0 ≤ E ^ 2 * X := mul_nonneg (sq_nonneg E) hX
    nlinarith
  nlinarith
end PI.PolynomialProperness.CoreW
