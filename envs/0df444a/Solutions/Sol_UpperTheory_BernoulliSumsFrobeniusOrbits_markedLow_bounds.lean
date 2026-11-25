-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.markedLow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:03.440859+00:00
-- url     : https://prove2.me/submissions/43055242-d854-4954-a131-df0274310628

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLowBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (δ : ℝ) (r : ℕ), 0 < δ → δ ≤ 1 / 100 →
      (1 / 10 : ℝ) ^ (6 * r + 1) ≤ markedLow δ r (Formalism.MainNotions.G.goodU δ) ∧ markedLow δ r (Formalism.MainNotions.G.goodU δ) ≤ 1 := by
  intro δ r hδ hδ1
  unfold markedLow Formalism.MainNotions.G.goodU
  set u := ⌈1 / δ⌉₊ with hu
  have hu1 : 1 / δ ≤ (u : ℝ) := Nat.le_ceil _
  have hu2 : (u : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have huδ1 : 1 ≤ (u : ℝ) * δ := by
    have h := mul_le_mul_of_nonneg_right hu1 hδ.le
    rwa [one_div, inv_mul_cancel₀ hδ.ne'] at h
  have huδ2 : (u : ℝ) * δ ≤ 1 + δ := by
    have h := mul_le_mul_of_nonneg_right hu2.le hδ.le
    rwa [add_mul, one_div, inv_mul_cancel₀ hδ.ne', one_mul] at h
  have h1δ : 0 < 1 - δ := by linarith
  have hlog : -(δ / (1 - δ)) ≤ Real.log (1 - δ) := by
    have h := Real.one_sub_inv_le_log_of_pos h1δ
    have e : 1 - (1 - δ)⁻¹ = -(δ / (1 - δ)) := by
      field_simp
      ring
    rw [e] at h
    exact h
  have hexp : (1 - δ) ^ u = Real.exp (u * Real.log (1 - δ)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos h1δ u)]
  have hq : (u : ℝ) * δ / (1 - δ) ≤ 103 / 100 := by
    rw [div_le_iff₀ h1δ]
    nlinarith
  have hA : 3 / 10 ≤ (1 - δ) ^ u := by
    rw [hexp]
    have step : -(103 / 100 : ℝ) ≤ u * Real.log (1 - δ) := by
      have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
      have e2 : (u : ℝ) * (-(δ / (1 - δ))) = -((u : ℝ) * δ / (1 - δ)) := by ring
      linarith
    have hE : Real.exp (103 / 100) ≤ 10 / 3 := by
      have e3 : Real.exp (103 / 100) = Real.exp 1 * Real.exp (3 / 100) := by
        rw [← Real.exp_add]
        norm_num
      have h3 := Real.abs_exp_sub_one_sub_id_le (x := (3 / 100 : ℝ)) (by norm_num)
      have h4 : Real.exp (3 / 100) ≤ 1 + 3 / 100 + (3 / 100) ^ 2 := by
        have := (abs_le.mp h3).2
        linarith
      have h5 := Real.exp_one_lt_d9
      have h6 : 0 ≤ Real.exp (3 / 100) := (Real.exp_pos _).le
      have h7 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      rw [e3]
      nlinarith
    have hmono : Real.exp (-(103 / 100)) ≤ Real.exp (u * Real.log (1 - δ)) := Real.exp_le_exp.mpr step
    rw [Real.exp_neg] at hmono
    have hpos := Real.exp_pos (103 / 100 : ℝ)
    have hinv : 3 / 10 ≤ (Real.exp (103 / 100))⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hpos]
      norm_num
      linarith
    linarith
  have hqge : (u : ℝ) - 1 ≤ 2 * ((u / 2 : ℕ) : ℝ) := by
    have h : u ≤ 2 * (u / 2) + 1 := by omega
    have h' : (u : ℝ) ≤ 2 * ((u / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hqle : 2 * ((u / 2 : ℕ) : ℝ) ≤ u := by
    have h : 2 * (u / 2) ≤ u := Nat.mul_div_le u 2
    exact_mod_cast h
  have hP : (1 - δ) ^ u ≤ (1 - δ) ^ (u - 1) :=
    pow_le_pow_of_le_one h1δ.le (by linarith) (Nat.sub_le u 1)
  have hP1 : (1 - δ) ^ (u - 1) ≤ 1 := pow_le_one₀ h1δ.le (by linarith)
  have hP0 : 0 ≤ (1 - δ) ^ (u - 1) := pow_nonneg h1δ.le _
  have hq0 : (0 : ℝ) ≤ ((u / 2 : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  have hqδ : 99 / 200 ≤ ((u / 2 : ℕ) : ℝ) * δ := by nlinarith
  have hqδ2 : ((u / 2 : ℕ) : ℝ) * δ ≤ 1 := by nlinarith
  have eB : ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) =
      3 / 4 * ((((u / 2 : ℕ) : ℝ) * δ) * (1 - δ) ^ (u - 1)) := by ring
  have hB : 1 / 10 ≤ ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) := by
    rw [eB]
    have h := mul_le_mul hqδ (le_trans hA hP) (by norm_num) hq0
    linarith
  have hB1 : ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) ≤ 1 := by
    rw [eB]
    have h := mul_le_mul hqδ2 hP1 hP0 (by norm_num)
    linarith
  have hB0 : 0 ≤ ((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1) := by linarith
  have hA0 : 0 ≤ (1 - δ) ^ u := pow_nonneg h1δ.le _
  constructor
  · calc (1 / 10 : ℝ) ^ (6 * r + 1) = (1 / 10 : ℝ) ^ (3 * r + 1) * (1 / 10 : ℝ) ^ (3 * r) := by
          rw [← pow_add]
          congr 1
          ring
      _ ≤ ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)) ^ (3 * r) :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith) _) (pow_le_pow_left₀ (by norm_num) hB _)
            (by positivity) (pow_nonneg hA0 _)
  · exact mul_le_one₀ (pow_le_one₀ hA0 (pow_le_one₀ h1δ.le (by linarith))) (pow_nonneg hB0 _)
      (pow_le_one₀ hB0 hB1)
end UpperTheory.BernoulliSumsFrobeniusOrbits
