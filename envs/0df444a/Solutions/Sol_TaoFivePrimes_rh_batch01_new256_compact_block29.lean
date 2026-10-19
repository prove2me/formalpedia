-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block29
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:41:02.98336+00:00
-- url     : https://prove2.me/submissions/0fbe9ebb-0181-4d82-a703-4ab7baca8881

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block29Checks
theorem row00 : RHBatch01New256CompactReference.checked (928+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (928+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (928+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (928+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (928+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (928+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (928+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (928+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (928+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (928+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (928+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (928+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (928+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (928+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (928+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (928+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (928+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (928+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (928+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (928+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (928+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (928+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (928+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (928+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (928+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (928+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (928+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (928+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (928+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (928+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (928+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (928+31)=true := by decide +kernel
end RHBatch01New256Block29Checks

theorem solution : RHBatch01New256CompactReference.block 928 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block29Checks.row00,RHBatch01New256Block29Checks.row01,RHBatch01New256Block29Checks.row02,RHBatch01New256Block29Checks.row03,RHBatch01New256Block29Checks.row04,RHBatch01New256Block29Checks.row05,RHBatch01New256Block29Checks.row06,RHBatch01New256Block29Checks.row07,RHBatch01New256Block29Checks.row08,RHBatch01New256Block29Checks.row09,RHBatch01New256Block29Checks.row10,RHBatch01New256Block29Checks.row11,RHBatch01New256Block29Checks.row12,RHBatch01New256Block29Checks.row13,RHBatch01New256Block29Checks.row14,RHBatch01New256Block29Checks.row15,RHBatch01New256Block29Checks.row16,RHBatch01New256Block29Checks.row17,RHBatch01New256Block29Checks.row18,RHBatch01New256Block29Checks.row19,RHBatch01New256Block29Checks.row20,RHBatch01New256Block29Checks.row21,RHBatch01New256Block29Checks.row22,RHBatch01New256Block29Checks.row23,RHBatch01New256Block29Checks.row24,RHBatch01New256Block29Checks.row25,RHBatch01New256Block29Checks.row26,RHBatch01New256Block29Checks.row27,RHBatch01New256Block29Checks.row28,RHBatch01New256Block29Checks.row29,RHBatch01New256Block29Checks.row30,RHBatch01New256Block29Checks.row31]
#print axioms solution
