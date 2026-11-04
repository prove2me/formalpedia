-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBatchLayout.stage_cell_lt_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:13.30231+00:00
-- url     : https://prove2.me/submissions/0047d634-22ba-4c46-9bdc-16172898282c

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBatchLayout
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBatchLayout
open SubsetAddress LightZetaStages
namespace ThreeSum.LightBlockSourceBatchLayout
theorem _root_.solution {W cut base j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    stageBase base (downsetCap W cut) j+subsetRank S < base+family W cut := by
  have hr := subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
  calc
    _ < base+j*downsetCap W cut+downsetCap W cut := Nat.add_lt_add_left hr _
    _ = base+(j+1)*downsetCap W cut := by ring
    _ ≤ base+(W+1)*downsetCap W cut := Nat.add_le_add_left hm _
    _ = _ := rfl
end ThreeSum.LightBlockSourceBatchLayout
