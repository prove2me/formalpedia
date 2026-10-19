-- Prove2me | solution 1 for STVFriedmann.corollary1_order2_rest_points
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:10:31.028967+00:00
-- url     : https://prove2.me/submissions/2913c18f-7cc8-4a8f-bc9b-76a4ea6609c4

import Mathlib
import Definitions.Def_STVFriedmann_basic
open Filter Topology Real STVFriedmann

theorem solution :
    stvField2 restU2 = 0 ∧ stvField2 restM2 = 0 ∧ stvField2 restSM2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i; fin_cases i <;> simp [stvField2, restU2, restM2, restSM2] <;> norm_num
