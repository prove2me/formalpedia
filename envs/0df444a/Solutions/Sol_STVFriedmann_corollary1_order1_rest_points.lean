-- Prove2me | solution 1 for STVFriedmann.corollary1_order1_rest_points
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:10:23.016047+00:00
-- url     : https://prove2.me/submissions/d5005da1-175b-4353-b114-ba1eb83821ae

import Mathlib
import Definitions.Def_STVFriedmann_basic
open Filter Topology Real STVFriedmann

theorem solution :
    stvField1 restU1 = 0 ∧ stvField1 restM1 = 0 ∧ stvField1 restSM1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i; fin_cases i <;> simp [stvField1, restU1, restM1, restSM1] <;> norm_num
