-- Prove2me | solution 1 for Sqrt6KissingBound.Palomar.planar_kissingNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:42:02.454488+00:00
-- url     : https://prove2.me/submissions/0ac24664-252c-4918-8a03-26d2b14ccc35

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_isGreatest
import Theorems.Thm_Sqrt6KissingBound_kissingNumber_two_eq_six
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section
namespace Sqrt6KissingBound.Palomar
theorem _root_.solution :
    IsGreatest {m : ℕ | RealizableKissingCard 2 m} 6 := by
  simpa only [kissingNumber_two_eq_six] using
    (kissingNumber_isGreatest (n := 2) (by decide))
end Sqrt6KissingBound.Palomar
