-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block25
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:41:31.70763+00:00
-- url     : https://prove2.me/submissions/4db07cc1-7499-4525-8385-cea917b77f9f

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block25Checks
theorem row00 : RHBatch01New256CompactReference.checked (800+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (800+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (800+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (800+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (800+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (800+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (800+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (800+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (800+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (800+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (800+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (800+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (800+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (800+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (800+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (800+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (800+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (800+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (800+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (800+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (800+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (800+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (800+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (800+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (800+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (800+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (800+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (800+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (800+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (800+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (800+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (800+31)=true := by decide +kernel
end RHBatch01New256Block25Checks

theorem solution : RHBatch01New256CompactReference.block 800 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block25Checks.row00,RHBatch01New256Block25Checks.row01,RHBatch01New256Block25Checks.row02,RHBatch01New256Block25Checks.row03,RHBatch01New256Block25Checks.row04,RHBatch01New256Block25Checks.row05,RHBatch01New256Block25Checks.row06,RHBatch01New256Block25Checks.row07,RHBatch01New256Block25Checks.row08,RHBatch01New256Block25Checks.row09,RHBatch01New256Block25Checks.row10,RHBatch01New256Block25Checks.row11,RHBatch01New256Block25Checks.row12,RHBatch01New256Block25Checks.row13,RHBatch01New256Block25Checks.row14,RHBatch01New256Block25Checks.row15,RHBatch01New256Block25Checks.row16,RHBatch01New256Block25Checks.row17,RHBatch01New256Block25Checks.row18,RHBatch01New256Block25Checks.row19,RHBatch01New256Block25Checks.row20,RHBatch01New256Block25Checks.row21,RHBatch01New256Block25Checks.row22,RHBatch01New256Block25Checks.row23,RHBatch01New256Block25Checks.row24,RHBatch01New256Block25Checks.row25,RHBatch01New256Block25Checks.row26,RHBatch01New256Block25Checks.row27,RHBatch01New256Block25Checks.row28,RHBatch01New256Block25Checks.row29,RHBatch01New256Block25Checks.row30,RHBatch01New256Block25Checks.row31]
#print axioms solution
