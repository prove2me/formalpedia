-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_eventual_distance_density_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:13:35.4665+00:00
-- url     : https://prove2.me/submissions/fff95fab-582f-4146-906e-07dd8173a992

import Definitions.Def_QEC_Coding_QuantumTanner_LocalDescent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_DistanceBudgets
import Theorems.Thm_QEC_Coding_QuantumTanner_distanceLineError_le_real_bound
section
noncomputable section
namespace QEC.Coding.QuantumTanner
open Filter
private theorem eventual_power_margin
    (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∃ t : Nat, ∀ n : Nat, t ≤ n → 2 ≤ n ∧ (n : ℝ) ^ a < c * (n : ℝ) ^ b := by
  have hSmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually (gt_mem_nhds hc)
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : Nat => (n : ℝ)) atTop atTop).eventually hSmall
  obtain ⟨t, ht⟩ := eventually_atTop.mp hNat
  refine ⟨max t 2, ?_⟩
  intro n hn
  have hTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
  have hPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨hTwo, ?_⟩
  calc
    (n : ℝ) ^ a = (n : ℝ) ^ (-(b - a)) * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hPos]
      congr 1
      ring
    _ < c * (n : ℝ) ^ b := mul_lt_mul_of_pos_right
      (ht n ((Nat.le_max_left _ _).trans hn)) (Real.rpow_pos_of_pos hPos _)
end QEC.Coding.QuantumTanner
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Filter
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (delta epsilon : ℝ) (hDeltaDistance : 0 < delta) (hEpsilon : 0 < epsilon) :
    ∃ t : Nat, ∀ Delta : Nat, t ≤ Delta →
      2 ≤ Delta ∧
      (distanceLineError delta epsilon Delta : ℝ) +
        (Delta : ℝ) ^ ((1 : ℝ) / 2 - epsilon) / 2 ≤ delta * Delta / 2 := by
  obtain ⟨t, ht⟩ := eventual_power_margin ((1 : ℝ) / 2 - epsilon) 1
    (min (delta ^ 2 / 4) (delta / 2)) (by linarith) (by positivity)
  refine ⟨t, ?_⟩
  intro Delta hDegree
  obtain ⟨hTwo, hPower⟩ := ht Delta hDegree
  rw [Real.rpow_one] at hPower
  have hD : (0 : ℝ) < Delta := by exact_mod_cast (by omega : 0 < Delta)
  have hError := distanceLineError_le_real_bound delta epsilon Delta (by omega) hDeltaDistance
  have hLeft := hPower.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le)
  have hRight := hPower.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le)
  have hErrorSmall : (distanceLineError delta epsilon Delta : ℝ) < delta * Delta / 4 := by
    apply hError.trans_lt
    apply (div_lt_iff₀ hDeltaDistance).mpr
    nlinarith only [hLeft]
  exact ⟨hTwo, by linarith only [hErrorSmall, hRight]⟩
end QEC.Coding.QuantumTanner
