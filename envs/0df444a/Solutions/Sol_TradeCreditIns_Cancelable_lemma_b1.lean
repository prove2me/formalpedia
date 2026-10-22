-- Prove2me | solution 1 for TradeCreditIns.Cancelable.lemma_b1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:08:13.386149+00:00
-- url     : https://prove2.me/submissions/be769415-8251-4091-8af3-91ab4ff7aff1

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

open TradeCreditIns.Cancelable

theorem solution (P : Params) (κ : Contract) (hS : P.Standing)
    (hκ : κ.IsCancelable P) :
    InsurerMonitors P κ ↔
      ShipsCovered P κ P.βbar ∧
      insurerCostEffort P κ ≤ P.βbar * (P.r - κ.δ) ∧
      insurerCostEffort P κ ≤ κ.f := by
  classical
  obtain ⟨hθ, -, -, hβ0, h01, h12, -, -, -, -, hc⟩ := hS
  obtain ⟨hδ0, hδr, hf0, hfp⟩ := hκ
  have hβ : ∀ i, 0 ≤ P.β i := by
    intro i; fin_cases i <;> simp <;> linarith
  have hpos : 0 < insurerCostEffort P κ := by
    unfold insurerCostEffort
    have : 0 ≤ ∑ i, P.θ i *
        (if Cancels P κ (P.β i) then κ.f
         else if ShipsCovered P κ (P.β i) then P.β i * (P.r - κ.δ) else 0) := by
      apply Finset.sum_nonneg
      intro i _
      apply mul_nonneg (hθ i)
      split_ifs
      · exact hf0
      · exact mul_nonneg (hβ i) (by linarith)
      · exact le_refl 0
    linarith
  unfold InsurerMonitors insurerCostKeep
  constructor
  · rintro ⟨hk, hf, -⟩
    by_cases hsc : ShipsCovered P κ P.βbar
    · rw [if_pos hsc] at hk; exact ⟨hsc, hk, hf⟩
    · rw [if_neg hsc] at hk; linarith
  · rintro ⟨hsc, hk, hf⟩
    rw [if_pos hsc]
    exact ⟨hk, hf, le_trans hf hfp⟩
