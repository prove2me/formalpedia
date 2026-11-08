-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.odd_mul_pow_isBigO_evenPow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:01:57.58661+00:00
-- url     : https://prove2.me/submissions/90332248-48ff-4a20-b422-654e476b969e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p t : ℝ} (hp : 0 ≤ p) (ht : Real.sqrt p < t) :
    (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * p ^ n) =O[atTop]
      fun n : ℕ => t ^ (2 * n) := by
  have ht0 : 0 < t := (Real.sqrt_nonneg p).trans_lt ht
  have hpt : |p| < t ^ 2 := by
    rw [abs_of_nonneg hp]
    have hs := mul_self_lt_mul_self (Real.sqrt_nonneg p) ht
    rw [← pow_two, Real.sq_sqrt hp, ← pow_two] at hs
    exact hs
  have hn := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) 1 hpt).isBigO
  have hconst := (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
    (R := ℝ) 0 hpt).isBigO
  have hsum := (hn.const_mul_left 2).add hconst
  apply hsum.congr'
  · filter_upwards [] with n
    norm_num
    ring
  · filter_upwards [] with n
    rw [pow_mul]
end QEC.Coding.TannerLiftedProduct
