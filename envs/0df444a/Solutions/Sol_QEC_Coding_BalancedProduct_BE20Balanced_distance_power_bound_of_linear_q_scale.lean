-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Balanced.distance_power_bound_of_linear_q_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:53:54.024092+00:00
-- url     : https://prove2.me/submissions/11bc92f1-4719-4184-9f4e-f1ecd6b55959

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Balanced
theorem _root_.solution
    (q N d coefficient : Nat)
    (hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2)
    (hqd : q * (q ^ 2 - 1) ≤ coefficient * d) :
    N ^ 3 ≤ blocklengthCoefficient ^ 3 * coefficient ^ 5 * d ^ 5 := by
  let s := q ^ 2 - 1
  have hs : s ≤ q ^ 2 := Nat.sub_le _ _
  have hsCube : s ^ 3 ≤ (q * s) ^ 2 := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ ≤ q ^ 2 * s ^ 2 := Nat.mul_le_mul_right (s ^ 2) hs
      _ = (q * s) ^ 2 := by ring
  rw [hN]
  change (blocklengthCoefficient * q * s ^ 2) ^ 3 ≤ _
  calc
    (blocklengthCoefficient * q * s ^ 2) ^ 3 =
        blocklengthCoefficient ^ 3 * (q * s) ^ 3 * s ^ 3 := by ring
    _ ≤ blocklengthCoefficient ^ 3 * (q * s) ^ 3 * (q * s) ^ 2 :=
      Nat.mul_le_mul_left _ hsCube
    _ = blocklengthCoefficient ^ 3 * (q * s) ^ 5 := by ring
    _ ≤ blocklengthCoefficient ^ 3 * (coefficient * d) ^ 5 :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' hqd 5)
    _ = blocklengthCoefficient ^ 3 * coefficient ^ 5 * d ^ 5 := by ring
end QEC.Coding.BalancedProduct.BE20Balanced
