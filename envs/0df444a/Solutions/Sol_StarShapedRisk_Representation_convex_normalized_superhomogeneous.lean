-- Prove2me | solution 1 for StarShapedRisk.Representation.convex_normalized_superhomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T19:54:32.939748+00:00
-- url     : https://prove2.me/submissions/ef1a821f-56e3-4720-9909-42f0afee9b7a

import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f) (h0 : f 0 = 0)
    {t : ℝ} (ht : 1 < t) (X : E) :
    t * f X ≤ f (t • X) := by
  have ht_pos : 0 < t := by linarith
  have ht_ne : t ≠ 0 := by linarith
  have ha_nonneg : 0 ≤ 1 / t := by positivity
  have ha_le_one : 1 / t ≤ 1 := by
    rw [div_le_iff₀ ht_pos]
    linarith
  have hb_nonneg : 0 ≤ 1 - 1 / t := by linarith
  have hab : (1 / t) + (1 - 1 / t) = 1 := by ring
  have h_comb : (1 / t) • (t • X) + (1 - 1 / t) • (0 : E) = X := by
    rw [smul_smul, smul_zero, add_zero]
    have h1 : (1 / t) * t = 1 := by field_simp
    rw [h1, one_smul]
  have h_le := hconv.2 (Set.mem_univ (t • X)) (Set.mem_univ (0 : E)) ha_nonneg hb_nonneg hab
  simp only [smul_eq_mul] at h_le
  rw [h_comb, h0, mul_zero, add_zero] at h_le
  have h_mul := mul_le_mul_of_nonneg_left h_le (le_of_lt ht_pos)
  have h_simp : t * (1 / t * f (t • X)) = f (t • X) := by
    calc t * (1 / t * f (t • X)) = (t * (1 / t)) * f (t • X) := by ring
    _ = 1 * f (t • X) := by
      have : t * (1 / t) = 1 := by field_simp
      rw [this]
    _ = f (t • X) := by ring
  rw [h_simp] at h_mul
  exact h_mul
