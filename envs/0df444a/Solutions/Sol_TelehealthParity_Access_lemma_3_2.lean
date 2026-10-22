-- Prove2me | solution 2 for TelehealthParity.Access.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:05:05.907998+00:00
-- url     : https://prove2.me/submissions/f70068ad-6599-4bb2-8b4e-3629b4cec80b

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting
set_option autoImplicit false
open TelehealthParity.Access

theorem solution (p : Params) (hp : p.Standing) (q : ℝ) (hq : 0 < q)
    (hκ : 0 < kappa p q) (hκ' : kappa p q ≤ 1 / (1 + Real.sqrt q) ^ 2) :
    0 ≤ (1 - kappa p q * (1 - q)) ^ 2 - 4 * q * kappa p q ∧ thetaBar p q < 1 := by
  set k := kappa p q with hk
  set s := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hsq : s ^ 2 = q := Real.sq_sqrt hq.le
  have h1 : k * (1 + s) ^ 2 ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hκ'
  have h2 : 0 ≤ 1 - k * (1 - s) ^ 2 := by nlinarith [mul_nonneg hκ.le hs0]
  have hD : (1 - k * (1 - q)) ^ 2 - 4 * q * k = (1 - k * (1 + s) ^ 2) * (1 - k * (1 - s) ^ 2) := by
    linear_combination (2 * k + k ^ 2 * (2 - q - s ^ 2)) * hsq
  have hD0 : 0 ≤ (1 - k * (1 - q)) ^ 2 - 4 * q * k := by
    rw [hD]; exact mul_nonneg (by linarith) h2
  refine ⟨hD0, ?_⟩
  have hpos : 0 < 1 - k * (1 - q) := by nlinarith [mul_pos hκ hq, mul_nonneg hκ.le hs0]
  have hlt : Real.sqrt ((1 - k * (1 - q)) ^ 2 - 4 * q * k) < 1 - k * (1 - q) := by
    rw [Real.sqrt_lt' hpos]
    nlinarith [mul_pos hq hκ]
  unfold thetaBar
  rw [← hk]
  linarith
