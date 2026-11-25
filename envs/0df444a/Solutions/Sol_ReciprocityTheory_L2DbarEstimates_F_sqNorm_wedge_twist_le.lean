-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.sqNorm_wedge_twist_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:05:55.593147+00:00
-- url     : https://prove2.me/submissions/f11a0357-8a02-4531-89c8-b9ae860a96bc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_norm_add_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} (a : ℂ) (A : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (B : V n) :
    sq2 n (fun j k => a * A j k + a * wedge c (fun i => B i) j k) ≤
      ‖a‖ ^ 2 * (2 + 4 * ∑ j, ‖c j‖ ^ 2) * (sq2 n A + ‖B‖ ^ 2) := by
  simp only [sq2, wedge]
  have hB : ‖B‖ ^ 2 = ∑ i, ‖B i‖ ^ 2 := EuclideanSpace.norm_sq_eq B
  have h1 : ∀ j k, ‖c j * B k - c k * B j‖ ^ 2 ≤
      2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2) := by
    intro j k
    have h := unwBack_norm_add_sq (c j * B k) (-(c k * B j))
    rw [← sub_eq_add_neg, norm_neg, norm_mul, norm_mul, mul_pow, mul_pow] at h
    linarith
  have e2 : ∑ j, ∑ k, ‖c k‖ ^ 2 * ‖B j‖ ^ 2 = ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 :=
    Finset.sum_comm
  have e3 : ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 = (∑ j, ‖c j‖ ^ 2) * ∑ k, ‖B k‖ ^ 2 := by
    rw [Finset.sum_mul_sum]
  have hW : ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2 ≤ 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
    calc ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2
        ≤ ∑ j, ∑ k, (2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h1 j k
      _ = 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [e2, e3, hB]
          simp only [← Finset.sum_mul]
          ring
  have hA : ∀ j k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) := by
    intro j k
    rw [← mul_add, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (unwBack_norm_add_sq _ _) (by positivity)
  have hsum : ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ∑ j, ∑ k, ‖A j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2) := by
    calc ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2
        ≤ ∑ j, ∑ k, ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hA j k
      _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  have hα : 0 ≤ ‖a‖ ^ 2 := by positivity
  have hS : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hSA : 0 ≤ ∑ j, ∑ k, ‖A j k‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have hb : 0 ≤ ‖B‖ ^ 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hW hα
  have k2 := mul_nonneg hα hb
  have k3 := mul_nonneg (mul_nonneg hα hS) hSA
  nlinarith [hsum, k1, k2, k3]
end ReciprocityTheory.L2DbarEstimates.F
