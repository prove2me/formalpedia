-- Prove2me | solution 1 for Sqrt6KissingBound.realizableKissingCard_le_kissingNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:37:07.373805+00:00
-- url     : https://prove2.me/submissions/b4ee420e-e614-4d91-9391-ac118c3b5d32

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingConfiguration_card_le_floor_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n m : ℕ} (hn : 1 ≤ n)
    (hm : RealizableKissingCard n m) : m ≤ kissingNumber n := by
  classical
  rcases hm with ⟨X, hX, rfl⟩
  apply Nat.le_findGreatest
  · exact kissingConfiguration_card_le_floor_sqrt6_pow hn X hX
  · exact ⟨X, hX, rfl⟩
end Sqrt6KissingBound
