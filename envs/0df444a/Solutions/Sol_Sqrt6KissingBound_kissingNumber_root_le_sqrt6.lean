-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_root_le_sqrt6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:36:45.359328+00:00
-- url     : https://prove2.me/submissions/cf536e5b-d4fb-4b91-a559-e8989724020a

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_realized
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_root_le_sqrt6


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹) ≤ Real.sqrt 6 := by
  rcases kissingNumber_realized n with ⟨X, hX, hcard⟩
  rw [← hcard]
  exact kissingConfiguration_root_le_sqrt6 hn X hX
end Sqrt6KissingBound
