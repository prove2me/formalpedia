-- Prove2me | solution 1 for Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:34:18.158305+00:00
-- url     : https://prove2.me/submissions/17089ddb-4cb7-45d9-9d28-88dfa3dfff78

import Definitions.Def_Sqrt6KissingBound_DimensionOne
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Definitions.Def_Sqrt6KissingBound_KissingBound
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_cube
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_dim_one
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_fifth
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_fourth
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_high
import Theorems.Thm_Sqrt6KissingBound_code_card_le_sqrt6_sq
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n := by
  rcases hX with ⟨hunit, hsep⟩
  by_cases hn5 : n ≤ 5
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · simpa using code_card_le_sqrt6_dim_one X hunit
    · simpa using code_card_le_sqrt6_sq X hunit hsep
    · simpa using code_card_le_sqrt6_cube X hunit hsep
    · simpa using code_card_le_sqrt6_fourth X hunit hsep
    · simpa using code_card_le_sqrt6_fifth X hunit hsep
  · have hn6 : 6 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n by omega)
    exact code_card_le_sqrt6_high (by omega) X hunit hsep
end Sqrt6KissingBound
