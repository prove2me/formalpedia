-- Prove2me | solution 1 for RHX100000.Slab.clear
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T23:02:43.637938+00:00
-- url     : https://prove2.me/submissions/5d171ff4-a1ce-401f-a469-5a02adc27350

import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_RHX100000_Slab_cell_0
import Theorems.Thm_RHX100000_Slab_cell_1
import Theorems.Thm_RHX100000_Slab_cell_2
import Theorems.Thm_RHX100000_Slab_cell_3
import Theorems.Thm_RHX100000_Slab_cell_4
import Theorems.Thm_RHX100000_Slab_cell_5
import Theorems.Thm_RHX100000_Slab_cell_6
import Theorems.Thm_RHX100000_Slab_cell_7
import Theorems.Thm_RHX_cellOK_of
import Theorems.Thm_RHX_edgeRest_of
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Arb4 Arb4.Q

theorem RHX100000.Slab.head : slabHeadOK RHX100000.Slab.S = true := by decide +kernel

theorem RHX100000.Slab.ok : slabOK RHX100000.Slab.S = true := by
  refine RHX.slabOK_of _ RHX100000.Slab.head (fun j hj => ?_)
  have hm : RHX100000.Slab.S.m = 8 := rfl
  rw [hm] at hj
  interval_cases j
  · exact RHX100000.Slab.cell_0
  · exact RHX100000.Slab.cell_1
  · exact RHX100000.Slab.cell_2
  · exact RHX100000.Slab.cell_3
  · exact RHX100000.Slab.cell_4
  · exact RHX100000.Slab.cell_5
  · exact RHX100000.Slab.cell_6
  · exact RHX100000.Slab.cell_7

theorem RHX100000.Slab.clear :
    EdgeClearGlue.SlabClear (100000 : ℝ) ((100000 : ℝ) + 3 / 1000) := by
  have h := Arb4.slabOK_sound RHX100000.Slab.S RHX100000.Slab.ok
  have hlo : RHX100000.Slab.S.lo.val = (100000 : ℝ) := by
    simp [RHX100000.Slab.S, Arb4.Q.val, Arb4.Q.ofNat]
  have hhi : RHX100000.Slab.S.hi.val = (100000 : ℝ) + 3 / 1000 := by
    simp [RHX100000.Slab.S, Arb4.Q.val, Arb4.Q.ofNat, Arb4.Q.add, Arb4.Q.frac]; norm_num
  rw [hlo, hhi] at h
  exact h
open Arb4 Arb4.Q in
theorem solution :
    EdgeClearGlue.SlabClear (100000 : ℝ) ((100000 : ℝ) + 3 / 1000) := by
  apply RHX100000.Slab.clear <;> assumption
