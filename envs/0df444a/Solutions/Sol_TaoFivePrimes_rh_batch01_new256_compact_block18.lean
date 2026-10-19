-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block18
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:39:21.016495+00:00
-- url     : https://prove2.me/submissions/6c4800cf-be4d-4742-8efe-0256eee9e116

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block18Checks
theorem row00 : RHBatch01New256CompactReference.checked (576+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (576+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (576+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (576+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (576+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (576+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (576+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (576+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (576+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (576+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (576+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (576+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (576+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (576+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (576+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (576+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (576+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (576+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (576+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (576+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (576+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (576+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (576+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (576+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (576+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (576+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (576+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (576+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (576+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (576+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (576+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (576+31)=true := by decide +kernel
end RHBatch01New256Block18Checks

theorem solution : RHBatch01New256CompactReference.block 576 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block18Checks.row00,RHBatch01New256Block18Checks.row01,RHBatch01New256Block18Checks.row02,RHBatch01New256Block18Checks.row03,RHBatch01New256Block18Checks.row04,RHBatch01New256Block18Checks.row05,RHBatch01New256Block18Checks.row06,RHBatch01New256Block18Checks.row07,RHBatch01New256Block18Checks.row08,RHBatch01New256Block18Checks.row09,RHBatch01New256Block18Checks.row10,RHBatch01New256Block18Checks.row11,RHBatch01New256Block18Checks.row12,RHBatch01New256Block18Checks.row13,RHBatch01New256Block18Checks.row14,RHBatch01New256Block18Checks.row15,RHBatch01New256Block18Checks.row16,RHBatch01New256Block18Checks.row17,RHBatch01New256Block18Checks.row18,RHBatch01New256Block18Checks.row19,RHBatch01New256Block18Checks.row20,RHBatch01New256Block18Checks.row21,RHBatch01New256Block18Checks.row22,RHBatch01New256Block18Checks.row23,RHBatch01New256Block18Checks.row24,RHBatch01New256Block18Checks.row25,RHBatch01New256Block18Checks.row26,RHBatch01New256Block18Checks.row27,RHBatch01New256Block18Checks.row28,RHBatch01New256Block18Checks.row29,RHBatch01New256Block18Checks.row30,RHBatch01New256Block18Checks.row31]
#print axioms solution
