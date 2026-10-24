-- Prove2me | solution 1 for PricingWithTips.minimumTip_le_requiredTip_off_order_with_tips
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:52:39.845818+00:00
-- url     : https://prove2.me/submissions/cef86592-c81b-4442-803a-54a8a420a3ce

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w t : B → S → ℝ) (uBar : D → ℝ)
    (b : B) (s : S)
    (hoff : ¬ A.Delivers b s)
    (hwzero : w b s = 0)
    (ht_nonneg : ∀ b' s', 0 ≤ t b' s')
    (hu_nonneg : ∀ d, 0 ≤ uBar d)
    (hupper : ∀ d b' s', w b' s' + t b' s' - M.cost d b' s' ≤ uBar d) :
    minimumTip M w t b s ≤ requiredTip M A uBar b s := by
  let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w t b s τ d}
  have hT_bdd : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro x ⟨hx, _⟩
    exact hx
  have hbound : ∀ d, minimumTip M w t b s ≤ M.cost d b s + uBar d := by
    intro d
    let τ : ℝ := M.cost d b s + uBar d
    have hτnonneg : 0 ≤ τ := by
      dsimp [τ]
      linarith [M.cost_nonneg d b s, hu_nonneg d]
    have hτmem : τ ∈ T := by
      refine ⟨hτnonneg, d, ?_⟩
      constructor
      · dsimp [τ]
        rw [hwzero]
        linarith [hu_nonneg d]
      · intro b' s'
        by_cases hb : b' = b
        · subst b'
          by_cases hs : s' = s
          · subst s'
            simp [counterfactualTip]
          · simp [counterfactualTip, hs, hwzero, τ]
            linarith [hupper d b s', ht_nonneg b s']
        · simp [counterfactualTip, hb, hwzero, τ]
          linarith [hupper d b' s']
    change sInf T ≤ τ
    exact csInf_le hT_bdd hτmem
  simp only [requiredTip, if_neg hoff]
  apply le_ciInf
  exact hbound
