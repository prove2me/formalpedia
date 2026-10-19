-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block14
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:17:36.744238+00:00
-- url     : https://prove2.me/submissions/5ba3c315-71e2-4c06-88fe-92ff46cb193c

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block14Checks
theorem row00 : RHBatch01New256CompactReference.checked (448+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (448+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (448+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (448+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (448+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (448+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (448+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (448+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (448+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (448+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (448+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (448+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (448+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (448+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (448+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (448+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (448+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (448+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (448+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (448+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (448+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (448+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (448+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (448+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (448+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (448+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (448+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (448+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (448+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (448+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (448+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (448+31)=true := by decide +kernel
end RHBatch01New256Block14Checks

theorem solution : RHBatch01New256CompactReference.block 448 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block14Checks.row00,RHBatch01New256Block14Checks.row01,RHBatch01New256Block14Checks.row02,RHBatch01New256Block14Checks.row03,RHBatch01New256Block14Checks.row04,RHBatch01New256Block14Checks.row05,RHBatch01New256Block14Checks.row06,RHBatch01New256Block14Checks.row07,RHBatch01New256Block14Checks.row08,RHBatch01New256Block14Checks.row09,RHBatch01New256Block14Checks.row10,RHBatch01New256Block14Checks.row11,RHBatch01New256Block14Checks.row12,RHBatch01New256Block14Checks.row13,RHBatch01New256Block14Checks.row14,RHBatch01New256Block14Checks.row15,RHBatch01New256Block14Checks.row16,RHBatch01New256Block14Checks.row17,RHBatch01New256Block14Checks.row18,RHBatch01New256Block14Checks.row19,RHBatch01New256Block14Checks.row20,RHBatch01New256Block14Checks.row21,RHBatch01New256Block14Checks.row22,RHBatch01New256Block14Checks.row23,RHBatch01New256Block14Checks.row24,RHBatch01New256Block14Checks.row25,RHBatch01New256Block14Checks.row26,RHBatch01New256Block14Checks.row27,RHBatch01New256Block14Checks.row28,RHBatch01New256Block14Checks.row29,RHBatch01New256Block14Checks.row30,RHBatch01New256Block14Checks.row31]
#print axioms solution
