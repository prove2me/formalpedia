-- Prove2me | solution 1 for RHX1000000.Slab.clear
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:38:22.596369+00:00
-- url     : https://prove2.me/submissions/b781c36c-7be4-479f-a99b-110c215a8899

import Theorems.Thm_Arb4_slabOK_sound
import Theorems.Thm_RHX1000000_Slab_cell_00
import Theorems.Thm_RHX1000000_Slab_cell_01
import Theorems.Thm_RHX1000000_Slab_cell_02
import Theorems.Thm_RHX1000000_Slab_cell_03
import Theorems.Thm_RHX1000000_Slab_cell_04
import Theorems.Thm_RHX1000000_Slab_cell_05
import Theorems.Thm_RHX1000000_Slab_cell_06
import Theorems.Thm_RHX1000000_Slab_cell_07
import Theorems.Thm_RHX1000000_Slab_cell_08
import Theorems.Thm_RHX1000000_Slab_cell_09
import Theorems.Thm_RHX_slabOK_of
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Arb4 Arb4.Q

theorem RHX1000000.Slab.head : slabHeadOK RHX1000000.Slab.S = true := by decide +kernel

theorem RHX1000000.Slab.ok : slabOK RHX1000000.Slab.S = true := by
  refine RHX.slabOK_of _ RHX1000000.Slab.head (fun j hj => ?_)
  have hm : RHX1000000.Slab.S.m = 10 := rfl
  rw [hm] at hj
  interval_cases j
  · exact RHX1000000.Slab.cell_00
  · exact RHX1000000.Slab.cell_01
  · exact RHX1000000.Slab.cell_02
  · exact RHX1000000.Slab.cell_03
  · exact RHX1000000.Slab.cell_04
  · exact RHX1000000.Slab.cell_05
  · exact RHX1000000.Slab.cell_06
  · exact RHX1000000.Slab.cell_07
  · exact RHX1000000.Slab.cell_08
  · exact RHX1000000.Slab.cell_09

theorem RHX1000000.Slab.clear :
    EdgeClearGlue.SlabClear (1000000 : ℝ) ((1000000 : ℝ) + 3 / 1000) := by
  have h := Arb4.slabOK_sound RHX1000000.Slab.S RHX1000000.Slab.ok
  have hlo : RHX1000000.Slab.S.lo.val = (1000000 : ℝ) := by
    simp [RHX1000000.Slab.S, Arb4.Q.val, Arb4.Q.ofNat]
  have hhi : RHX1000000.Slab.S.hi.val = (1000000 : ℝ) + 3 / 1000 := by
    simp [RHX1000000.Slab.S, Arb4.Q.val, Arb4.Q.ofNat, Arb4.Q.add, Arb4.Q.frac]; norm_num
  rw [hlo, hhi] at h
  exact h
open Arb4 Arb4.Q in
theorem solution :
    EdgeClearGlue.SlabClear (1000000 : ℝ) ((1000000 : ℝ) + 3 / 1000) := by
  apply RHX1000000.Slab.clear <;> assumption
