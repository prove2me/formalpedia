-- Prove2me | solution 1 for PI.PolynomialProperness.add_le_mul_pow_of_sq_le_of_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:03:56.959119+00:00
-- url     : https://prove2.me/submissions/ebdedddd-6db5-4eac-8a9d-33095c36f156

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
theorem _root_.solution {Cc D a s sp x : ℝ} {e N : ℕ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hs1 : 1 ≤ s) (hx : 1 ≤ x)
    (hs : s ^ 2 ≤ Cc * (1 + D * x ^ (2 * e + 2)) ^ 2) (hsp : sp ≤ a * s * x) (hN : 4 * e + 5 ≤ N) :
    s + sp ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ s := by linarith
  set K := 2 * e + 2 with hK
  have hxK : 1 ≤ x ^ K := one_le_pow₀ hx
  have hA : 1 + D * x ^ K ≤ (1 + D) * x ^ K := by nlinarith
  have hA0 : 0 ≤ 1 + D * x ^ K := by nlinarith
  have hs_le : s ≤ s ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 := by
    calc s ^ 2 ≤ Cc * (1 + D * x ^ K) ^ 2 := hs
      _ ≤ |Cc| * (1 + D * x ^ K) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) (abs_nonneg _)
  have hsx : s ≤ |Cc| * (1 + D) ^ 2 * x ^ (2 * K) := by
    have e2 : ((1 + D) * x ^ K) ^ 2 = (1 + D) ^ 2 * x ^ (2 * K) := by ring
    rw [e2] at hs2
    nlinarith
  have hxN : x ^ (2 * K + 1) ≤ x ^ N := pow_le_pow_right₀ hx (by omega)
  have hB0 : 0 ≤ |Cc| * (1 + D) ^ 2 := by positivity
  calc s + sp ≤ s + a * s * x := by linarith
    _ ≤ (1 + a) * x * s := by nlinarith
    _ ≤ (1 + a) * x * (|Cc| * (1 + D) ^ 2 * x ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left hsx (mul_nonneg (by linarith) hx0)
    _ = (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ (2 * K + 1) := by ring
    _ ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N :=
        mul_le_mul_of_nonneg_left hxN (mul_nonneg (by linarith) hB0)
end PI.PolynomialProperness
