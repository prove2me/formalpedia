-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block26
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:42:56.981034+00:00
-- url     : https://prove2.me/submissions/2712fcf4-e1c0-45a2-a32b-395f5c52dd62

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block26Checks
theorem row00 : RHBatch01New256CompactReference.checked (832+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (832+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (832+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (832+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (832+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (832+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (832+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (832+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (832+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (832+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (832+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (832+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (832+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (832+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (832+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (832+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (832+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (832+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (832+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (832+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (832+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (832+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (832+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (832+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (832+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (832+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (832+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (832+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (832+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (832+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (832+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (832+31)=true := by decide +kernel
end RHBatch01New256Block26Checks

theorem solution : RHBatch01New256CompactReference.block 832 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block26Checks.row00,RHBatch01New256Block26Checks.row01,RHBatch01New256Block26Checks.row02,RHBatch01New256Block26Checks.row03,RHBatch01New256Block26Checks.row04,RHBatch01New256Block26Checks.row05,RHBatch01New256Block26Checks.row06,RHBatch01New256Block26Checks.row07,RHBatch01New256Block26Checks.row08,RHBatch01New256Block26Checks.row09,RHBatch01New256Block26Checks.row10,RHBatch01New256Block26Checks.row11,RHBatch01New256Block26Checks.row12,RHBatch01New256Block26Checks.row13,RHBatch01New256Block26Checks.row14,RHBatch01New256Block26Checks.row15,RHBatch01New256Block26Checks.row16,RHBatch01New256Block26Checks.row17,RHBatch01New256Block26Checks.row18,RHBatch01New256Block26Checks.row19,RHBatch01New256Block26Checks.row20,RHBatch01New256Block26Checks.row21,RHBatch01New256Block26Checks.row22,RHBatch01New256Block26Checks.row23,RHBatch01New256Block26Checks.row24,RHBatch01New256Block26Checks.row25,RHBatch01New256Block26Checks.row26,RHBatch01New256Block26Checks.row27,RHBatch01New256Block26Checks.row28,RHBatch01New256Block26Checks.row29,RHBatch01New256Block26Checks.row30,RHBatch01New256Block26Checks.row31]
#print axioms solution
