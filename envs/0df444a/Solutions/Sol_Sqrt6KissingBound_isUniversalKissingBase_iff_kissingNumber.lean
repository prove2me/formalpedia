-- Prove2me | solution 1 for Sqrt6KissingBound.isUniversalKissingBase_iff_kissingNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:40:47.585565+00:00
-- url     : https://prove2.me/submissions/33ccac6a-7c2b-44e0-a744-2b85d47bec2e

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_realized
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_kissingNumber

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (α : ℝ) :
    IsUniversalKissingBase α ↔
      0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n := by
  constructor
  · intro hα
    refine ⟨hα.1, ?_⟩
    intro n hn
    rcases kissingNumber_realized n with ⟨X, hX, hcard⟩
    rw [← hcard]
    exact hα.2 hn X hX
  · rintro ⟨hα, hbound⟩
    refine ⟨hα, ?_⟩
    intro n hn X hX
    have hcard : (X.card : ℝ) ≤ kissingNumber n := by
      exact_mod_cast kissingConfiguration_card_le_kissingNumber hn X hX
    exact hcard.trans (hbound n hn)
end Sqrt6KissingBound
