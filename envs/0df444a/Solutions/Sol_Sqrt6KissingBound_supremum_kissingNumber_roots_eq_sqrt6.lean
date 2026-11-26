-- Prove2me | solution 1 for Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:42:01.77504+00:00
-- url     : https://prove2.me/submissions/173c428c-4a47-4d45-8596-53220faba04f

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_two_eq_six
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_root_le_sqrt6

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by
  have hmem : Real.sqrt 6 ∈
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
        r = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)} := by
    refine ⟨2, by norm_num, ?_⟩
    rw [kissingNumber_two_eq_six, Real.sqrt_eq_rpow]
    norm_num
  apply le_antisymm
  · apply csSup_le
    · exact ⟨Real.sqrt 6, hmem⟩
    · rintro r ⟨n, hn, rfl⟩
      exact kissingNumber_root_le_sqrt6 hn
  · apply le_csSup
    · refine ⟨Real.sqrt 6, ?_⟩
      rintro r ⟨n, hn, rfl⟩
      exact kissingNumber_root_le_sqrt6 hn
    · exact hmem
end Sqrt6KissingBound
