-- Prove2me | solution 1 for Sqrt6KissingBound.Palomar.kissingNumber_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:42:58.644663+00:00
-- url     : https://prove2.me/submissions/371059ea-a98c-4dcd-8323-1529542044f1

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_isGreatest
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_supremum_kissingNumber_roots_eq_sqrt6
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section
namespace Sqrt6KissingBound.Palomar
theorem _root_.solution (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by
  have heq : ∀ n : ℕ, 1 ≤ n → τ n = kissingNumber n := by
    intro n hn
    exact le_antisymm
      ((kissingNumber_isGreatest hn).2 (hτ n hn).1)
      ((hτ n hn).2 (kissingNumber_isGreatest hn).1)
  have hset :
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} =
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
        r = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)} := by
    ext r
    constructor
    · rintro ⟨n, hn, hr⟩
      exact ⟨n, hn, by simpa only [heq n hn] using hr⟩
    · rintro ⟨n, hn, hr⟩
      exact ⟨n, hn, by simpa only [heq n hn] using hr⟩
  rw [hset]
  exact supremum_kissingNumber_roots_eq_sqrt6
end Sqrt6KissingBound.Palomar
