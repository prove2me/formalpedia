-- Prove2me | solution 1 for Sqrt6KissingBound.Palomar.kissingNumber_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:41:40.45138+00:00
-- url     : https://prove2.me/submissions/7e1aeaed-7434-4e2c-9db7-280e7fcfe9a6

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_isGreatest
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_le_sqrt6_pow


set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section
namespace Sqrt6KissingBound.Palomar
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, IsGreatest {m : ℕ | RealizableKissingCard n m} k ∧
      (k : ℝ) ≤ (Real.sqrt 6) ^ n := by
  exact ⟨kissingNumber n, kissingNumber_isGreatest hn,
    kissingNumber_le_sqrt6_pow hn⟩
end Sqrt6KissingBound.Palomar
