-- Prove2me | solution 1 for ThreeSum.LightTernaryParallelBudget.dictionary_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:58.147971+00:00
-- url     : https://prove2.me/submissions/5909164b-2c99-4ffb-8bf6-0c19cd0e3252

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelBudget
import Theorems.Thm_ThreeSum_LightTernaryParallelBudget_radix_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelBudget
namespace ThreeSum.LightTernaryParallelBudget
theorem _root_.solution (xs : List ℤ) (hm : 1≤xs.length) (J : ℕ) :
    LightFixedRadixDictionary.time xs J ≤ 1000*(J+1)*(xs.length^J+xs.length+1) := by
  have ht := radix_time_bound xs.length hm J
  have hmono : xs.length+1 ≤ (J+1)*(xs.length^J+xs.length+1) := by
    calc
      xs.length+1 ≤ xs.length^J+xs.length+1 := by omega
      _ ≤ (J+1)*(xs.length^J+xs.length+1) := Nat.le_mul_of_pos_left _ (by omega)
  unfold LightFixedRadixDictionary.time
  nlinarith
end ThreeSum.LightTernaryParallelBudget
