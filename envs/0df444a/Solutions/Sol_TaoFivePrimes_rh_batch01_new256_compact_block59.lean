-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block59
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:39:08.361147+00:00
-- url     : https://prove2.me/submissions/0d5a7a3f-9fe6-45b3-9d3c-dcadf2e507f3

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block59Checks
theorem row00 : RHBatch01New256CompactReference.checked (1888+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1888+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1888+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1888+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1888+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1888+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1888+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1888+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1888+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1888+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1888+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1888+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1888+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1888+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1888+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1888+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1888+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1888+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1888+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1888+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1888+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1888+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1888+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1888+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1888+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1888+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1888+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1888+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1888+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1888+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1888+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1888+31)=true := by decide +kernel
end RHBatch01New256Block59Checks

theorem solution : RHBatch01New256CompactReference.block 1888 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block59Checks.row00,RHBatch01New256Block59Checks.row01,RHBatch01New256Block59Checks.row02,RHBatch01New256Block59Checks.row03,RHBatch01New256Block59Checks.row04,RHBatch01New256Block59Checks.row05,RHBatch01New256Block59Checks.row06,RHBatch01New256Block59Checks.row07,RHBatch01New256Block59Checks.row08,RHBatch01New256Block59Checks.row09,RHBatch01New256Block59Checks.row10,RHBatch01New256Block59Checks.row11,RHBatch01New256Block59Checks.row12,RHBatch01New256Block59Checks.row13,RHBatch01New256Block59Checks.row14,RHBatch01New256Block59Checks.row15,RHBatch01New256Block59Checks.row16,RHBatch01New256Block59Checks.row17,RHBatch01New256Block59Checks.row18,RHBatch01New256Block59Checks.row19,RHBatch01New256Block59Checks.row20,RHBatch01New256Block59Checks.row21,RHBatch01New256Block59Checks.row22,RHBatch01New256Block59Checks.row23,RHBatch01New256Block59Checks.row24,RHBatch01New256Block59Checks.row25,RHBatch01New256Block59Checks.row26,RHBatch01New256Block59Checks.row27,RHBatch01New256Block59Checks.row28,RHBatch01New256Block59Checks.row29,RHBatch01New256Block59Checks.row30,RHBatch01New256Block59Checks.row31]
#print axioms solution
