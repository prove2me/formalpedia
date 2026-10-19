-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block28
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:43:25.971589+00:00
-- url     : https://prove2.me/submissions/1a31fcc2-59e0-453a-9591-a1e160065919

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block28Checks
theorem row00 : RHBatch01New256CompactReference.checked (896+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (896+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (896+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (896+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (896+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (896+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (896+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (896+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (896+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (896+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (896+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (896+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (896+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (896+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (896+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (896+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (896+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (896+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (896+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (896+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (896+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (896+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (896+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (896+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (896+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (896+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (896+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (896+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (896+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (896+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (896+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (896+31)=true := by decide +kernel
end RHBatch01New256Block28Checks

theorem solution : RHBatch01New256CompactReference.block 896 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block28Checks.row00,RHBatch01New256Block28Checks.row01,RHBatch01New256Block28Checks.row02,RHBatch01New256Block28Checks.row03,RHBatch01New256Block28Checks.row04,RHBatch01New256Block28Checks.row05,RHBatch01New256Block28Checks.row06,RHBatch01New256Block28Checks.row07,RHBatch01New256Block28Checks.row08,RHBatch01New256Block28Checks.row09,RHBatch01New256Block28Checks.row10,RHBatch01New256Block28Checks.row11,RHBatch01New256Block28Checks.row12,RHBatch01New256Block28Checks.row13,RHBatch01New256Block28Checks.row14,RHBatch01New256Block28Checks.row15,RHBatch01New256Block28Checks.row16,RHBatch01New256Block28Checks.row17,RHBatch01New256Block28Checks.row18,RHBatch01New256Block28Checks.row19,RHBatch01New256Block28Checks.row20,RHBatch01New256Block28Checks.row21,RHBatch01New256Block28Checks.row22,RHBatch01New256Block28Checks.row23,RHBatch01New256Block28Checks.row24,RHBatch01New256Block28Checks.row25,RHBatch01New256Block28Checks.row26,RHBatch01New256Block28Checks.row27,RHBatch01New256Block28Checks.row28,RHBatch01New256Block28Checks.row29,RHBatch01New256Block28Checks.row30,RHBatch01New256Block28Checks.row31]
#print axioms solution
