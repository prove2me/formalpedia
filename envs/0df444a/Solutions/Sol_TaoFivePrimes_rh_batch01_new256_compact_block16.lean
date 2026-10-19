-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block16
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:32:50.802619+00:00
-- url     : https://prove2.me/submissions/8dcb3ccd-429c-4e96-8622-a718587d005e

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block16Checks
theorem row00 : RHBatch01New256CompactReference.checked (512+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (512+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (512+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (512+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (512+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (512+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (512+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (512+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (512+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (512+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (512+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (512+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (512+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (512+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (512+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (512+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (512+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (512+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (512+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (512+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (512+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (512+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (512+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (512+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (512+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (512+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (512+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (512+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (512+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (512+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (512+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (512+31)=true := by decide +kernel
end RHBatch01New256Block16Checks

theorem solution : RHBatch01New256CompactReference.block 512 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block16Checks.row00,RHBatch01New256Block16Checks.row01,RHBatch01New256Block16Checks.row02,RHBatch01New256Block16Checks.row03,RHBatch01New256Block16Checks.row04,RHBatch01New256Block16Checks.row05,RHBatch01New256Block16Checks.row06,RHBatch01New256Block16Checks.row07,RHBatch01New256Block16Checks.row08,RHBatch01New256Block16Checks.row09,RHBatch01New256Block16Checks.row10,RHBatch01New256Block16Checks.row11,RHBatch01New256Block16Checks.row12,RHBatch01New256Block16Checks.row13,RHBatch01New256Block16Checks.row14,RHBatch01New256Block16Checks.row15,RHBatch01New256Block16Checks.row16,RHBatch01New256Block16Checks.row17,RHBatch01New256Block16Checks.row18,RHBatch01New256Block16Checks.row19,RHBatch01New256Block16Checks.row20,RHBatch01New256Block16Checks.row21,RHBatch01New256Block16Checks.row22,RHBatch01New256Block16Checks.row23,RHBatch01New256Block16Checks.row24,RHBatch01New256Block16Checks.row25,RHBatch01New256Block16Checks.row26,RHBatch01New256Block16Checks.row27,RHBatch01New256Block16Checks.row28,RHBatch01New256Block16Checks.row29,RHBatch01New256Block16Checks.row30,RHBatch01New256Block16Checks.row31]
#print axioms solution
