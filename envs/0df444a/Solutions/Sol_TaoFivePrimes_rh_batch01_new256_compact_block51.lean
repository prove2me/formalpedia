-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block51
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:31:43.024092+00:00
-- url     : https://prove2.me/submissions/e9bb0ba2-a84e-48b1-aa28-d5da7cf4b910

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block51Checks
theorem row00 : RHBatch01New256CompactReference.checked (1632+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1632+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1632+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1632+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1632+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1632+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1632+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1632+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1632+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1632+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1632+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1632+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1632+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1632+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1632+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1632+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1632+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1632+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1632+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1632+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1632+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1632+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1632+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1632+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1632+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1632+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1632+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1632+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1632+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1632+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1632+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1632+31)=true := by decide +kernel
end RHBatch01New256Block51Checks

theorem solution : RHBatch01New256CompactReference.block 1632 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block51Checks.row00,RHBatch01New256Block51Checks.row01,RHBatch01New256Block51Checks.row02,RHBatch01New256Block51Checks.row03,RHBatch01New256Block51Checks.row04,RHBatch01New256Block51Checks.row05,RHBatch01New256Block51Checks.row06,RHBatch01New256Block51Checks.row07,RHBatch01New256Block51Checks.row08,RHBatch01New256Block51Checks.row09,RHBatch01New256Block51Checks.row10,RHBatch01New256Block51Checks.row11,RHBatch01New256Block51Checks.row12,RHBatch01New256Block51Checks.row13,RHBatch01New256Block51Checks.row14,RHBatch01New256Block51Checks.row15,RHBatch01New256Block51Checks.row16,RHBatch01New256Block51Checks.row17,RHBatch01New256Block51Checks.row18,RHBatch01New256Block51Checks.row19,RHBatch01New256Block51Checks.row20,RHBatch01New256Block51Checks.row21,RHBatch01New256Block51Checks.row22,RHBatch01New256Block51Checks.row23,RHBatch01New256Block51Checks.row24,RHBatch01New256Block51Checks.row25,RHBatch01New256Block51Checks.row26,RHBatch01New256Block51Checks.row27,RHBatch01New256Block51Checks.row28,RHBatch01New256Block51Checks.row29,RHBatch01New256Block51Checks.row30,RHBatch01New256Block51Checks.row31]
#print axioms solution
