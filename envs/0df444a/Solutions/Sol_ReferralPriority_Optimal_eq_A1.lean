-- Prove2me | solution 1 for ReferralPriority.Optimal.eq_A1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:14:30.669395+00:00
-- url     : https://prove2.me/submissions/4e23f2b3-8eee-49d8-b50a-1904c308694f

import Mathlib
import Definitions.Def_ReferralPriority_Optimal_Model

open ReferralPriority.Optimal in
theorem solution (E : Env) (hS : E.Standing) (Lam : ℝ) (hL0 : 0 < Lam) (W1 W0 r α : ℝ)
    (h : SBFeasible E Lam W1 W0 r α) (hr : 0 < r) (hα : 0 < α) :
    0 ≤ E.V - E.k / α - E.c / (E.mu * (1 - r * α) - Lam * r * α ^ 2) := by
  obtain ⟨⟨hW1, hW0, ⟨hr0, hr1⟩, ⟨hα0, hα1⟩, hIR, _, hOA6b, _, _⟩, hIC⟩ := h
  obtain ⟨hmu, hc, hk, _⟩ := hS
  have h0 := hIC 0 ⟨le_refl _, zero_le_one⟩
  unfold payoff at h0
  unfold IR payoff at hIR
  unfold OA6b at hOA6b
  have hs : E.k + E.c * α * (W1 - W0) ≤ 0 := by
    by_contra hc'
    push_neg at hc'
    nlinarith [mul_pos hr hc']
  have hii : 0 ≤ E.V - E.k - E.c * α * W1 - E.c * (1 - α) * W0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - r) (by linarith : (0:ℝ) ≤ -(E.k + E.c * α * (W1 - W0)))]
  have key : 0 ≤ α * E.V - E.k - α * E.c * W1 := by
    nlinarith [mul_nonneg hα0 hii, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α)
      (by linarith : (0:ℝ) ≤ -(E.k + E.c * α * (W1 - W0)))]
  have hcd : E.c / (E.mu * (1 - r * α) - Lam * r * α ^ 2) ≤ E.c * W1 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hOA6b hc.le
  have h2 : 0 ≤ (α * E.V - E.k - α * E.c * W1) / α := div_nonneg key hα.le
  have e : (α * E.V - E.k - α * E.c * W1) / α = E.V - E.k / α - E.c * W1 := by
    field_simp
  linarith
