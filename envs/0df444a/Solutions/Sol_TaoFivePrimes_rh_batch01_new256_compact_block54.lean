-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block54
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:34:01.277253+00:00
-- url     : https://prove2.me/submissions/138313f4-0d22-4e0f-9e4a-119a87b5164a

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block54Checks
theorem row00 : RHBatch01New256CompactReference.checked (1728+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1728+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1728+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1728+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1728+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1728+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1728+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1728+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1728+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1728+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1728+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1728+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1728+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1728+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1728+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1728+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1728+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1728+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1728+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1728+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1728+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1728+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1728+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1728+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1728+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1728+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1728+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1728+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1728+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1728+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1728+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1728+31)=true := by decide +kernel
end RHBatch01New256Block54Checks

theorem solution : RHBatch01New256CompactReference.block 1728 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block54Checks.row00,RHBatch01New256Block54Checks.row01,RHBatch01New256Block54Checks.row02,RHBatch01New256Block54Checks.row03,RHBatch01New256Block54Checks.row04,RHBatch01New256Block54Checks.row05,RHBatch01New256Block54Checks.row06,RHBatch01New256Block54Checks.row07,RHBatch01New256Block54Checks.row08,RHBatch01New256Block54Checks.row09,RHBatch01New256Block54Checks.row10,RHBatch01New256Block54Checks.row11,RHBatch01New256Block54Checks.row12,RHBatch01New256Block54Checks.row13,RHBatch01New256Block54Checks.row14,RHBatch01New256Block54Checks.row15,RHBatch01New256Block54Checks.row16,RHBatch01New256Block54Checks.row17,RHBatch01New256Block54Checks.row18,RHBatch01New256Block54Checks.row19,RHBatch01New256Block54Checks.row20,RHBatch01New256Block54Checks.row21,RHBatch01New256Block54Checks.row22,RHBatch01New256Block54Checks.row23,RHBatch01New256Block54Checks.row24,RHBatch01New256Block54Checks.row25,RHBatch01New256Block54Checks.row26,RHBatch01New256Block54Checks.row27,RHBatch01New256Block54Checks.row28,RHBatch01New256Block54Checks.row29,RHBatch01New256Block54Checks.row30,RHBatch01New256Block54Checks.row31]
#print axioms solution
