-- Prove2me | solution 1 for PricingWithTips.minimum_cost_full_assignment_has_plan
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:35:49.71151+00:00
-- url     : https://prove2.me/submissions/0c39492a-94a0-47e2-a895-611e69a51e55

import Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_has_dual_potentials

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    ∃ w, IsCourierPlanFor M A w := by
  classical
  obtain ⟨C, u, v, hu, hdual, htight⟩ :=
    minimum_cost_full_assignment_has_dual_potentials M A hfull hminimum
  let w : B → S → ℝ := fun b s => if A.Delivers b s then C - v b s else 0
  have hw : ∀ b s, 0 ≤ w b s := by
    intro b s
    by_cases hd : A.Delivers b s
    · obtain ⟨d, htrade⟩ := hd
      have hd' : A.Delivers b s := ⟨d, htrade⟩
      have heq := htight d b s htrade
      simp only [w, if_pos hd']
      linarith [hu d, M.cost_nonneg d b s]
    · simp [w, hd]
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · intro d b s htrade
    have hd : A.Delivers b s := ⟨d, htrade⟩
    have hmain : w b s - M.cost d b s = u d := by
      simp only [w, if_pos hd]
      linarith [htight d b s htrade]
    constructor
    · rw [hmain]
      exact hu d
    · intro b' s'
      rw [hmain]
      by_cases hd' : A.Delivers b' s'
      · simp only [w, if_pos hd']
        linarith [hdual d b' s']
      · simp only [w, if_neg hd']
        linarith [hu d, M.cost_nonneg d b' s']
  · intro d hnot
    exact (hnot (hfull d)).elim
  · intro b s hnot
    simp [w, hnot]
