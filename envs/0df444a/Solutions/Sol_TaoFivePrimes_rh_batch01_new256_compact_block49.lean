-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block49
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:30:45.301108+00:00
-- url     : https://prove2.me/submissions/0005ee5a-5162-463c-a438-7113a0242d0b

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block49Checks
theorem row00 : RHBatch01New256CompactReference.checked (1568+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1568+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1568+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1568+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1568+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1568+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1568+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1568+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1568+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1568+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1568+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1568+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1568+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1568+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1568+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1568+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1568+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1568+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1568+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1568+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1568+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1568+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1568+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1568+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1568+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1568+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1568+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1568+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1568+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1568+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1568+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1568+31)=true := by decide +kernel
end RHBatch01New256Block49Checks

theorem solution : RHBatch01New256CompactReference.block 1568 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block49Checks.row00,RHBatch01New256Block49Checks.row01,RHBatch01New256Block49Checks.row02,RHBatch01New256Block49Checks.row03,RHBatch01New256Block49Checks.row04,RHBatch01New256Block49Checks.row05,RHBatch01New256Block49Checks.row06,RHBatch01New256Block49Checks.row07,RHBatch01New256Block49Checks.row08,RHBatch01New256Block49Checks.row09,RHBatch01New256Block49Checks.row10,RHBatch01New256Block49Checks.row11,RHBatch01New256Block49Checks.row12,RHBatch01New256Block49Checks.row13,RHBatch01New256Block49Checks.row14,RHBatch01New256Block49Checks.row15,RHBatch01New256Block49Checks.row16,RHBatch01New256Block49Checks.row17,RHBatch01New256Block49Checks.row18,RHBatch01New256Block49Checks.row19,RHBatch01New256Block49Checks.row20,RHBatch01New256Block49Checks.row21,RHBatch01New256Block49Checks.row22,RHBatch01New256Block49Checks.row23,RHBatch01New256Block49Checks.row24,RHBatch01New256Block49Checks.row25,RHBatch01New256Block49Checks.row26,RHBatch01New256Block49Checks.row27,RHBatch01New256Block49Checks.row28,RHBatch01New256Block49Checks.row29,RHBatch01New256Block49Checks.row30,RHBatch01New256Block49Checks.row31]
#print axioms solution
