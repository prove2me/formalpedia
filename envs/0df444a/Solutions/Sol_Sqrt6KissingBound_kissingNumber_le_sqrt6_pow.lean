-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_le_sqrt6_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:35:49.558967+00:00
-- url     : https://prove2.me/submissions/14d6e0a0-6448-4f6d-9c25-29ac40eb9363

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_realized
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n := by
  rcases kissingNumber_realized n with ⟨X, hX, hcard⟩
  rw [← hcard]
  exact kissingConfiguration_card_le_sqrt6_pow hn X hX
end Sqrt6KissingBound
