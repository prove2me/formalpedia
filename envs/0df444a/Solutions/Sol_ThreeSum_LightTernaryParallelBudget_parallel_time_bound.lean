-- Prove2me | solution 1 for ThreeSum.LightTernaryParallelBudget.parallel_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:06.75521+00:00
-- url     : https://prove2.me/submissions/b581bd15-a65a-42d0-aab7-6fcb92466d13

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelBudget
import Theorems.Thm_ThreeSum_LightTernaryParallelBudget_dictionary_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelBudget
namespace ThreeSum.LightTernaryParallelBudget
theorem _root_.solution (xs ys zs : List ℤ) (hxy : ys.length=xs.length)
    (hxz : zs.length=xs.length) (hm : 1≤xs.length) (J : ℕ) :
    LightTernaryParallelDictionaries.time xs ys zs J ≤
      4000*(J+1)*(xs.length^J+xs.length+1) := by
  have h0 := dictionary_time_bound xs hm J
  have h1 := dictionary_time_bound ys (by omega) J
  have h2 := dictionary_time_bound zs (by omega) J
  have hpos : 1 ≤ (J+1)*(xs.length^J+xs.length+1) := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  rw [hxy] at h1
  rw [hxz] at h2
  unfold LightTernaryParallelDictionaries.time
  nlinarith
end ThreeSum.LightTernaryParallelBudget
