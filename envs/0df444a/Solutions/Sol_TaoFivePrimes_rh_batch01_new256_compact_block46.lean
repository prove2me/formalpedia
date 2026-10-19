-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block46
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:28:24.942468+00:00
-- url     : https://prove2.me/submissions/5866db3f-0d02-4060-9b4f-22c5c7b53954

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block46Checks
theorem row00 : RHBatch01New256CompactReference.checked (1472+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1472+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1472+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1472+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1472+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1472+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1472+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1472+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1472+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1472+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1472+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1472+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1472+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1472+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1472+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1472+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1472+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1472+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1472+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1472+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1472+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1472+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1472+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1472+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1472+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1472+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1472+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1472+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1472+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1472+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1472+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1472+31)=true := by decide +kernel
end RHBatch01New256Block46Checks

theorem solution : RHBatch01New256CompactReference.block 1472 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block46Checks.row00,RHBatch01New256Block46Checks.row01,RHBatch01New256Block46Checks.row02,RHBatch01New256Block46Checks.row03,RHBatch01New256Block46Checks.row04,RHBatch01New256Block46Checks.row05,RHBatch01New256Block46Checks.row06,RHBatch01New256Block46Checks.row07,RHBatch01New256Block46Checks.row08,RHBatch01New256Block46Checks.row09,RHBatch01New256Block46Checks.row10,RHBatch01New256Block46Checks.row11,RHBatch01New256Block46Checks.row12,RHBatch01New256Block46Checks.row13,RHBatch01New256Block46Checks.row14,RHBatch01New256Block46Checks.row15,RHBatch01New256Block46Checks.row16,RHBatch01New256Block46Checks.row17,RHBatch01New256Block46Checks.row18,RHBatch01New256Block46Checks.row19,RHBatch01New256Block46Checks.row20,RHBatch01New256Block46Checks.row21,RHBatch01New256Block46Checks.row22,RHBatch01New256Block46Checks.row23,RHBatch01New256Block46Checks.row24,RHBatch01New256Block46Checks.row25,RHBatch01New256Block46Checks.row26,RHBatch01New256Block46Checks.row27,RHBatch01New256Block46Checks.row28,RHBatch01New256Block46Checks.row29,RHBatch01New256Block46Checks.row30,RHBatch01New256Block46Checks.row31]
#print axioms solution
