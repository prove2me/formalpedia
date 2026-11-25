-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.real_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:29.411336+00:00
-- url     : https://prove2.me/submissions/05207a13-3570-4028-af7e-7a6607c5083f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {d F Ssq Wsq C1 B2 c m6 : ℝ} {T n : ℕ} (hnT' : n < T) (hd : 0 ≤ d)
    (hF0 : 0 ≤ F) (hF : F ≤ (C1 * d ^ (T - n)) ^ 2 * B2) (hB2 : 0 ≤ B2) (hc : 0 < c)
    (hS : c * d ^ 2 ≤ Ssq) (hm : 0 < m6) (hW : m6 ≤ Wsq) :
    F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ)) ≤
      (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
        d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
  have hnT : n ≤ T := hnT'.le
  have hK : 0 ≤ C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) := by positivity
  rcases hd.eq_or_lt with h0 | hdpos
  · subst h0
    have hz : (0:ℝ) ^ (T - n) = 0 := zero_pow (by omega)
    rw [hz, mul_zero] at hF
    have hF' : F = 0 := le_antisymm (by simpa using hF) hF0
    rw [hF', zero_mul, zero_mul]
    positivity
  · have hSpos : 0 < Ssq := lt_of_lt_of_le (by positivity) hS
    have h1 : Ssq ^ (-((T : ℝ) - 1 / 2)) ≤ (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by
        have : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
        linarith)
    have h2 : Wsq ^ (-(1 / 2 : ℝ)) ≤ m6 ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hm hW (by norm_num)
    calc F * Ssq ^ (-((T : ℝ) - 1 / 2)) * Wsq ^ (-(1 / 2 : ℝ))
        ≤ ((C1 * d ^ (T - n)) ^ 2 * B2) * (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) *
            m6 ^ (-(1 / 2 : ℝ)) := by
          have hW0 : 0 ≤ Wsq ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (hm.le.trans hW) _
          have hS0 : 0 ≤ Ssq ^ (-((T : ℝ) - 1 / 2)) := Real.rpow_nonneg hSpos.le _
          gcongr
      _ = (C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ))) *
            d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
          have e1 : (d ^ (T - n)) ^ 2 = d ^ (2 * ((T : ℝ) - n)) := by
            rw [← pow_mul, ← Real.rpow_natCast]
            congr 1
            push_cast [Nat.cast_sub hnT]
            ring
          have e2 : (c * d ^ 2) ^ (-((T : ℝ) - 1 / 2)) =
              c ^ (-((T : ℝ) - 1 / 2)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) := by
            rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hd]
            push_cast
            ring_nf
          have e3 : d ^ (2 * ((T : ℝ) - n)) * d ^ (-2 * ((T : ℝ) - 1 / 2)) =
              d ^ (-2 * ((n : ℝ) - 1 / 2)) := by
            rw [← Real.rpow_add hdpos]; ring_nf
          rw [mul_pow, e1, e2]
          rw [← e3]
          ring
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
