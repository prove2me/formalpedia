-- Prove2me | solution 1 for TelehealthParity.Access.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-21T13:02:11.367448+00:00
-- url     : https://prove2.me/submissions/9b53bc7c-7908-4d3f-8680-2f74598a6fd3

import Definitions.Def_TelehealthParity_Access_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Daily21Telehealth

theorem scalar_bound (q k : ℝ) (hq : 0 < q) (hk : 0 < k)
    (hcap : k ≤ 1 / (1 + Real.sqrt q) ^ 2) :
    0 ≤ (1 - k * (1 - q)) ^ 2 - 4 * q * k ∧
      (1 + k * (1 - q) + Real.sqrt ((1 - k * (1 - q)) ^ 2 - 4 * q * k)) / 2 < 1 := by
  let s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.2 hq
  have hsq : s ^ 2 = q := Real.sq_sqrt hq.le
  have hden : 0 < (1 + s) ^ 2 := sq_pos_of_pos (by linarith)
  have hcap' : k * (1 + s) ^ 2 ≤ 1 := (le_div_iff₀ hden).1 hcap
  have hf1 : 0 ≤ 1 - k * (1 + s) ^ 2 := by linarith
  have hf2 : 0 ≤ 1 - k * (1 - s) ^ 2 := by
    nlinarith [mul_pos hk hs]
  have hfactor : (1 - k * (1 - q)) ^ 2 - 4 * q * k =
      (1 - k * (1 + s) ^ 2) * (1 - k * (1 - s) ^ 2) := by
    rw [← hsq]
    ring
  have hD : 0 ≤ (1 - k * (1 - q)) ^ 2 - 4 * q * k := by
    rw [hfactor]
    exact mul_nonneg hf1 hf2
  have ha : 0 < 1 - k * (1 - q) := by
    have hgap : k * (1 + s) ^ 2 = k * (1 - q) + 2 * k * s * (1 + s) := by
      rw [← hsq]
      ring
    have hgap_pos : 0 < 2 * k * s * (1 + s) := by positivity
    linarith
  have hroot : Real.sqrt ((1 - k * (1 - q)) ^ 2 - 4 * q * k) <
      1 - k * (1 - q) := by
    have hroot0 := Real.sqrt_nonneg ((1 - k * (1 - q)) ^ 2 - 4 * q * k)
    have hroot2 := Real.sq_sqrt hD
    nlinarith [mul_pos hq hk]
  constructor
  · exact hD
  · linarith

end Daily21Telehealth

open TelehealthParity.Access

theorem solution (p : Params) (hp : p.Standing) (q : ℝ) (hq : 0 < q)
    (hκ : 0 < kappa p q) (hκ' : kappa p q ≤ 1 / (1 + Real.sqrt q) ^ 2) :
    0 ≤ (1 - kappa p q * (1 - q)) ^ 2 - 4 * q * kappa p q ∧ thetaBar p q < 1 := by
  exact Daily21Telehealth.scalar_bound q (kappa p q) hq hκ hκ'

#print axioms solution
