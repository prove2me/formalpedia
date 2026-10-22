-- Prove2me | solution 1 for PlatformFinance.EndogRate.G1_nonneg_low_cost
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:51:10.327714+00:00
-- url     : https://prove2.me/submissions/c65d6965-e259-4987-a5aa-607ad1faccb1

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model
set_option autoImplicit false
open PlatformFinance.EndogRate

theorem solution (a φ c rf : ℝ) (ha : 0 < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hcost : c ≤ cbar a φ rf) :
    ∀ r : ℝ, -1 < r → r ≤ rf → 0 ≤ G1 a φ c rf r := by
  intro r hr1 hr2
  have hs : 0 < 1 + rf := by linarith
  have hu : 0 < 1 + r := by linarith
  have hus : 1 + r ≤ 1 + rf := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  have hx : c * (1 + rf) ≤ a * (1 - φ) ^ 2 := by
    unfold cbar at hcost
    rw [le_div_iff₀ hs] at hcost
    exact hcost
  set s := 1 + rf with hsdef
  set u := 1 + r with hudef
  have hK0 : 0 ≤ a ^ 2 * (1 - φ) ^ 3 * s := by positivity
  have hB : 0 ≤ c * (2 - φ) := by
    have : 0 ≤ 2 - φ := by linarith
    positivity
  -- T = G1 at r = rf
  have hT : 0 ≤ c * s ^ 2 * (-a * (1 - φ) * φ + c * (1 - φ) * s - c * (2 - φ) * s)
      + a ^ 2 * (1 - φ) ^ 3 * s := by
    have e : c * s ^ 2 * (-a * (1 - φ) * φ + c * (1 - φ) * s - c * (2 - φ) * s)
        + a ^ 2 * (1 - φ) ^ 3 * s
        = s * ((a * (1 - φ) ^ 2 - c * s) * (c * s + a * (1 - φ) ^ 2 + a * φ * (1 - φ))) := by
      ring
    rw [e]
    have h2 : 0 ≤ a * (1 - φ) ^ 2 - c * s := by linarith
    have h3 : 0 ≤ c * s + a * (1 - φ) ^ 2 + a * φ * (1 - φ) := by positivity
    positivity
  have key : s ^ 2 * G1 a φ c rf r
      = c * (c * (2 - φ)) * u ^ 2 * (s - u) * s ^ 2
        + u ^ 2 * (c * s ^ 2 * (-a * (1 - φ) * φ + c * (1 - φ) * s - c * (2 - φ) * s)
            + a ^ 2 * (1 - φ) ^ 3 * s)
        + a ^ 2 * (1 - φ) ^ 3 * s * (s ^ 2 - u ^ 2) := by
    unfold G1
    simp only [hsdef, hudef]
    ring
  have h1 : 0 ≤ c * (c * (2 - φ)) * u ^ 2 * (s - u) * s ^ 2 := by
    have : 0 ≤ s - u := by linarith
    positivity
  have h2 : 0 ≤ u ^ 2 * (c * s ^ 2 * (-a * (1 - φ) * φ + c * (1 - φ) * s - c * (2 - φ) * s)
            + a ^ 2 * (1 - φ) ^ 3 * s) := mul_nonneg (by positivity) hT
  have h3 : 0 ≤ a ^ 2 * (1 - φ) ^ 3 * s * (s ^ 2 - u ^ 2) := by
    apply mul_nonneg hK0
    nlinarith
  have hs2 : 0 < s ^ 2 := by positivity
  have : 0 ≤ s ^ 2 * G1 a φ c rf r := by rw [key]; linarith
  exact nonneg_of_mul_nonneg_right (by linarith) hs2 |> fun h => by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_neg_of_pos_of_neg hs2 hneg]
