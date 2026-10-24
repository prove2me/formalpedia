-- Prove2me | solution 1 for PricingWithTips.minimumTip_le_requiredTip_off_order
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:40:30.72642+00:00
-- url     : https://prove2.me/submissions/b243d5fc-b68d-4a5f-855c-6841bbda440b

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem minimumTip_le_cost_add_utility
    (M : Market B S D) (w : B → S → ℝ) (uBar : D → ℝ)
    (b : B) (s : S)
    (hwzero : w b s = 0)
    (hu_nonneg : ∀ d, 0 ≤ uBar d)
    (hupper : ∀ d b' s', w b' s' - M.cost d b' s' ≤ uBar d)
    (d : D) :
    minimumTip M w (fun _ _ => 0) b s ≤ M.cost d b s + uBar d := by
  let τ : ℝ := M.cost d b s + uBar d
  let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w (fun _ _ => 0) b s τ d}
  have hT_bdd : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro x ⟨hx, _⟩
    exact hx
  have hτnonneg : 0 ≤ τ := by
    dsimp [τ]
    linarith [M.cost_nonneg d b s, hu_nonneg d]
  have hτmem : τ ∈ T := by
    refine ⟨hτnonneg, d, ?_⟩
    constructor
    · dsimp [τ, courierUtility]
      rw [hwzero]
      linarith [hu_nonneg d]
    · intro b' s'
      by_cases hb : b' = b
      · subst b'
        by_cases hs : s' = s
        · subst s'
          simp [counterfactualTip]
        · simp [counterfactualTip, hs, hwzero, τ]
          linarith [hupper d b s']
      · simp [counterfactualTip, hb, hwzero, τ]
        linarith [hupper d b' s']
  change sInf T ≤ τ
  exact csInf_le hT_bdd hτmem

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (b : B) (s : S)
    (hoff : ¬ A.Delivers b s)
    (hwzero : w b s = 0)
    (hu_nonneg : ∀ d, 0 ≤ uBar d)
    (hupper : ∀ d b' s', w b' s' - M.cost d b' s' ≤ uBar d) :
    minimumTip M w (fun _ _ => 0) b s ≤ requiredTip M A uBar b s := by
  simp only [requiredTip, if_neg hoff]
  apply le_ciInf
  intro d
  exact minimumTip_le_cost_add_utility M w uBar b s hwzero hu_nonneg hupper d
