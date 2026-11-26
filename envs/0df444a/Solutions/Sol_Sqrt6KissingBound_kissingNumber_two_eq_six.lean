-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_two_eq_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:39:30.164383+00:00
-- url     : https://prove2.me/submissions/679f28b5-4b97-445d-a17d-e8fa5516f572

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_realized
import Theorems.Thm_Sqrt6KissingBound_realizableKissingCard_le_kissingNumber
import Theorems.Thm_Sqrt6KissingBound_code_card_le_six_dim_two
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_card
import Theorems.Thm_Sqrt6KissingBound_regularHexagon_isKissingConfiguration


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution : kissingNumber 2 = 6 := by
  apply le_antisymm
  · have hreal := kissingNumber_realized 2
    rcases hreal with ⟨X, hX, hcard⟩
    rw [← hcard]
    exact code_card_le_six_dim_two X hX.1 hX.2
  · apply realizableKissingCard_le_kissingNumber (n := 2) (m := 6) (by norm_num)
    exact ⟨regularHexagon, regularHexagon_isKissingConfiguration,
      regularHexagon_card⟩
end Sqrt6KissingBound
