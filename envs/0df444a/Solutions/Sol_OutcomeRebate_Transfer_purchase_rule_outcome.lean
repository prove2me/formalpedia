-- Prove2me | solution 1 for OutcomeRebate.Transfer.purchase_rule_outcome
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:41:21.459873+00:00
-- url     : https://prove2.me/submissions/811fdfc6-63a7-44aa-8df8-985b4939a783

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model

namespace OutcomeRebate.Transfer
open MeasureTheory

lemma obp_u_nonneg (α lam x : ℝ) (hx : 0 ≤ x) : u α lam x = x ^ α := by
  simp [u, hx]

lemma obp_u_neg (α lam x : ℝ) (hx : x < 0) : u α lam x = -(lam * (-x) ^ α) := by
  simp [u, not_le.mpr hx]

theorem obp_purchase_rule_outcome (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareO P bb p v ↔ bb * p ≤ v := by
  obtain ⟨_, _, _, hβ, hβh, hq0, hq1, hα0, hα1, hlam, _⟩ := hS
  unfold welfareO
  by_cases h : bb * p ≤ v
  · rw [obp_u_nonneg _ _ _ (by linarith)]
    simp only [h, iff_true]
    exact mul_nonneg hq0.le (Real.rpow_nonneg (by linarith) _)
  · push_neg at h
    rw [obp_u_neg _ _ _ (by linarith)]
    have : 0 < (-(v - bb * p)) ^ P.α := Real.rpow_pos_of_pos (by linarith) _
    constructor
    · intro h'
      exfalso
      nlinarith [mul_pos hq0 (mul_pos (by linarith : (0:ℝ) < P.lam) this)]
    · intro h'; linarith


end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) (bb p v : ℝ)
    (hbb : bb = P.β ∨ bb = 1) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ welfareO P bb p v ↔ bb * p ≤ v :=
  obp_purchase_rule_outcome P hS bb p v hbb hp hv
