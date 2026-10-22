-- Prove2me | solution 1 for TradeCreditIns.Cancelable.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:06:18.61384+00:00
-- url     : https://prove2.me/submissions/4dc0c061-66c3-4da3-8e0a-2b595e3a48c7

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model
import Theorems.Thm_TradeCreditIns_Cancelable_feasibility
import Theorems.Thm_TradeCreditIns_Cancelable_pi2_first_best
import Theorems.Thm_TradeCreditIns_Cancelable_upper_bound

open TradeCreditIns.Cancelable

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    Admissible P (κstar P) ∧
    (∀ i, Cancels P (κstar P) (P.β i) ↔ i ≠ 0) ∧
    (∀ i, Ships P (κstar P) (P.β i) ↔ i = 0) ∧
    supplierPayoff P (κstar P) = firstBest P ∧
    ∀ κ, Admissible P κ →
      supplierPayoff P κ ≤ supplierPayoff P (κstar P) := by
  obtain ⟨hadm, hcan, hship⟩ := feasibility P hS hA1 hA2 hcφ hr0
  obtain ⟨h1, h2⟩ := pi2_first_best P hS hA1 hA2 hcφ hr0
  have hfb : supplierPayoff P (κstar P) = firstBest P := h1.trans h2
  refine ⟨hadm, hcan, hship, hfb, ?_⟩
  intro κ hκ
  rw [hfb]
  exact upper_bound P hS κ hκ.1 hκ.2.1
