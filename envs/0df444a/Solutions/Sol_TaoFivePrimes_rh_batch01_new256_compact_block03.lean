-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block03
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:29:55.24756+00:00
-- url     : https://prove2.me/submissions/04ff18e3-6a36-4d9f-9c48-f7745a6a61d5

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block03Checks
theorem row00 : RHBatch01New256CompactReference.checked (96+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (96+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (96+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (96+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (96+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (96+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (96+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (96+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (96+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (96+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (96+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (96+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (96+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (96+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (96+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (96+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (96+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (96+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (96+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (96+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (96+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (96+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (96+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (96+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (96+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (96+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (96+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (96+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (96+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (96+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (96+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (96+31)=true := by decide +kernel
end RHBatch01New256Block03Checks

theorem solution : RHBatch01New256CompactReference.block 96 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block03Checks.row00,RHBatch01New256Block03Checks.row01,RHBatch01New256Block03Checks.row02,RHBatch01New256Block03Checks.row03,RHBatch01New256Block03Checks.row04,RHBatch01New256Block03Checks.row05,RHBatch01New256Block03Checks.row06,RHBatch01New256Block03Checks.row07,RHBatch01New256Block03Checks.row08,RHBatch01New256Block03Checks.row09,RHBatch01New256Block03Checks.row10,RHBatch01New256Block03Checks.row11,RHBatch01New256Block03Checks.row12,RHBatch01New256Block03Checks.row13,RHBatch01New256Block03Checks.row14,RHBatch01New256Block03Checks.row15,RHBatch01New256Block03Checks.row16,RHBatch01New256Block03Checks.row17,RHBatch01New256Block03Checks.row18,RHBatch01New256Block03Checks.row19,RHBatch01New256Block03Checks.row20,RHBatch01New256Block03Checks.row21,RHBatch01New256Block03Checks.row22,RHBatch01New256Block03Checks.row23,RHBatch01New256Block03Checks.row24,RHBatch01New256Block03Checks.row25,RHBatch01New256Block03Checks.row26,RHBatch01New256Block03Checks.row27,RHBatch01New256Block03Checks.row28,RHBatch01New256Block03Checks.row29,RHBatch01New256Block03Checks.row30,RHBatch01New256Block03Checks.row31]
#print axioms solution
