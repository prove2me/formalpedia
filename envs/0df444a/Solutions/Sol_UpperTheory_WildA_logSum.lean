-- Prove2me | solution 1 for UpperTheory.WildA.logSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:11.180926+00:00
-- url     : https://prove2.me/submissions/6c446685-065a-4fa4-a49a-c4fb47d9fbd2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_WildJets_LogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.WildA
theorem _root_.solution :
    ∀ y : ℝ, 1 ≤ y → ∑ l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.logb l y * Real.log l ≤ y * Real.log y := by
  intro y hy
  set S := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime with hS
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ l ∈ S, Real.logb l y * Real.log l = Real.log y := by
    intro l hl
    have hp : Nat.Prime l := (Finset.mem_filter.1 hl).2
    have h1 : (1:ℝ) < l := by exact_mod_cast hp.one_lt
    have hlog : Real.log l ≠ 0 := (Real.log_pos h1).ne'
    rw [Real.logb, div_mul_cancel₀ _ hlog]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlogy
  have hsub : S ⊆ (Finset.range (⌊y⌋₊ + 1)).erase 0 := by
    intro l hl
    rw [hS, Finset.mem_filter] at hl
    exact Finset.mem_erase.2 ⟨hl.2.ne_zero, hl.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
  have h2 : S.card ≤ ⌊y⌋₊ := by omega
  calc (S.card : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ y := Nat.floor_le (by linarith)
end UpperTheory.WildA
