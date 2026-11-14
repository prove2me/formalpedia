-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_pinned_expectation_monotone
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:12.20282+00:00
-- url     : https://prove2.me/submissions/4e30ca38-cb14-4a24-af35-9b9ccc6da9df

import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_reveal_nonnegative
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t s : ℝ) (d n : ℕ)
    (hπ : ∀ a, 0 ≤ m.pi t a) (hP : ∀ a b, 0 ≤ m.P t a b) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (f g : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ)
    (hfg : ∀ M σ U, f M σ U ≤ g M σ U) :
    plantedPinnedE m t s d n f ≤ plantedPinnedE m t s d n g := by
  classical
  unfold plantedPinnedE
  apply Finset.sum_le_sum
  intro M hM
  apply Finset.sum_le_sum
  intro σ hσ
  apply Finset.sum_le_sum
  intro U hU
  exact mul_le_mul_of_nonneg_left (hfg M σ U) (planted_reveal_nonnegative m t s d n hπ hP hs hs1 M σ U)
