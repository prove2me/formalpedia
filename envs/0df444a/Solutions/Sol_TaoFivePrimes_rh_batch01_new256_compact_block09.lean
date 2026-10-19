-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block09
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:44:05.120023+00:00
-- url     : https://prove2.me/submissions/fcb96c1f-c9c0-4bd1-8a8c-6c7d643b9d76

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block09Checks
theorem row00 : RHBatch01New256CompactReference.checked (288+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (288+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (288+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (288+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (288+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (288+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (288+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (288+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (288+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (288+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (288+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (288+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (288+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (288+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (288+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (288+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (288+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (288+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (288+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (288+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (288+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (288+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (288+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (288+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (288+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (288+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (288+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (288+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (288+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (288+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (288+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (288+31)=true := by decide +kernel
end RHBatch01New256Block09Checks

theorem solution : RHBatch01New256CompactReference.block 288 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block09Checks.row00,RHBatch01New256Block09Checks.row01,RHBatch01New256Block09Checks.row02,RHBatch01New256Block09Checks.row03,RHBatch01New256Block09Checks.row04,RHBatch01New256Block09Checks.row05,RHBatch01New256Block09Checks.row06,RHBatch01New256Block09Checks.row07,RHBatch01New256Block09Checks.row08,RHBatch01New256Block09Checks.row09,RHBatch01New256Block09Checks.row10,RHBatch01New256Block09Checks.row11,RHBatch01New256Block09Checks.row12,RHBatch01New256Block09Checks.row13,RHBatch01New256Block09Checks.row14,RHBatch01New256Block09Checks.row15,RHBatch01New256Block09Checks.row16,RHBatch01New256Block09Checks.row17,RHBatch01New256Block09Checks.row18,RHBatch01New256Block09Checks.row19,RHBatch01New256Block09Checks.row20,RHBatch01New256Block09Checks.row21,RHBatch01New256Block09Checks.row22,RHBatch01New256Block09Checks.row23,RHBatch01New256Block09Checks.row24,RHBatch01New256Block09Checks.row25,RHBatch01New256Block09Checks.row26,RHBatch01New256Block09Checks.row27,RHBatch01New256Block09Checks.row28,RHBatch01New256Block09Checks.row29,RHBatch01New256Block09Checks.row30,RHBatch01New256Block09Checks.row31]
#print axioms solution
