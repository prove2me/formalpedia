-- Prove2me | solution 1 for Sqrt6KissingBound.Palomar.kissingNumber_universal_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:44:47.462338+00:00
-- url     : https://prove2.me/submissions/dd91f6a6-b79d-430d-87d6-f1cf66229345

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_isGreatest
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_universal_base_iff
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section
namespace Sqrt6KissingBound.Palomar
theorem _root_.solution (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α := by
  have heq : ∀ n : ℕ, 1 ≤ n → τ n = kissingNumber n := by
    intro n hn
    exact le_antisymm
      ((kissingNumber_isGreatest hn).2 (hτ n hn).1)
      ((hτ n hn).2 (kissingNumber_isGreatest hn).1)
  have hiff :
      (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) := by
    constructor
    · rintro ⟨hα, hb⟩
      exact ⟨hα, fun n hn => by simpa only [heq n hn] using hb n hn⟩
    · rintro ⟨hα, hb⟩
      exact ⟨hα, fun n hn => by simpa only [heq n hn] using hb n hn⟩
  exact hiff.trans (kissingNumber_universal_base_iff α)
end Sqrt6KissingBound.Palomar
