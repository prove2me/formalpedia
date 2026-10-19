-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:38:20.277849+00:00
-- url     : https://prove2.me/submissions/6db959dc-b8f3-4fbf-80a9-44fcdf769419

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block05Checks
theorem row00 : RHBatch01New256CompactReference.checked (160+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (160+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (160+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (160+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (160+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (160+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (160+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (160+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (160+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (160+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (160+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (160+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (160+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (160+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (160+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (160+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (160+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (160+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (160+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (160+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (160+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (160+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (160+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (160+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (160+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (160+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (160+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (160+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (160+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (160+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (160+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (160+31)=true := by decide +kernel
end RHBatch01New256Block05Checks

theorem solution : RHBatch01New256CompactReference.block 160 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block05Checks.row00,RHBatch01New256Block05Checks.row01,RHBatch01New256Block05Checks.row02,RHBatch01New256Block05Checks.row03,RHBatch01New256Block05Checks.row04,RHBatch01New256Block05Checks.row05,RHBatch01New256Block05Checks.row06,RHBatch01New256Block05Checks.row07,RHBatch01New256Block05Checks.row08,RHBatch01New256Block05Checks.row09,RHBatch01New256Block05Checks.row10,RHBatch01New256Block05Checks.row11,RHBatch01New256Block05Checks.row12,RHBatch01New256Block05Checks.row13,RHBatch01New256Block05Checks.row14,RHBatch01New256Block05Checks.row15,RHBatch01New256Block05Checks.row16,RHBatch01New256Block05Checks.row17,RHBatch01New256Block05Checks.row18,RHBatch01New256Block05Checks.row19,RHBatch01New256Block05Checks.row20,RHBatch01New256Block05Checks.row21,RHBatch01New256Block05Checks.row22,RHBatch01New256Block05Checks.row23,RHBatch01New256Block05Checks.row24,RHBatch01New256Block05Checks.row25,RHBatch01New256Block05Checks.row26,RHBatch01New256Block05Checks.row27,RHBatch01New256Block05Checks.row28,RHBatch01New256Block05Checks.row29,RHBatch01New256Block05Checks.row30,RHBatch01New256Block05Checks.row31]
#print axioms solution
