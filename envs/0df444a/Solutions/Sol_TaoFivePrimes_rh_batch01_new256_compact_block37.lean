-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block37
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:11:58.868331+00:00
-- url     : https://prove2.me/submissions/40b9ea45-465b-4da4-9a46-172d56fcad05

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block37Checks
theorem row00 : RHBatch01New256CompactReference.checked (1184+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1184+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1184+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1184+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1184+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1184+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1184+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1184+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1184+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1184+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1184+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1184+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1184+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1184+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1184+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1184+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1184+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1184+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1184+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1184+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1184+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1184+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1184+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1184+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1184+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1184+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1184+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1184+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1184+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1184+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1184+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1184+31)=true := by decide +kernel
end RHBatch01New256Block37Checks

theorem solution : RHBatch01New256CompactReference.block 1184 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block37Checks.row00,RHBatch01New256Block37Checks.row01,RHBatch01New256Block37Checks.row02,RHBatch01New256Block37Checks.row03,RHBatch01New256Block37Checks.row04,RHBatch01New256Block37Checks.row05,RHBatch01New256Block37Checks.row06,RHBatch01New256Block37Checks.row07,RHBatch01New256Block37Checks.row08,RHBatch01New256Block37Checks.row09,RHBatch01New256Block37Checks.row10,RHBatch01New256Block37Checks.row11,RHBatch01New256Block37Checks.row12,RHBatch01New256Block37Checks.row13,RHBatch01New256Block37Checks.row14,RHBatch01New256Block37Checks.row15,RHBatch01New256Block37Checks.row16,RHBatch01New256Block37Checks.row17,RHBatch01New256Block37Checks.row18,RHBatch01New256Block37Checks.row19,RHBatch01New256Block37Checks.row20,RHBatch01New256Block37Checks.row21,RHBatch01New256Block37Checks.row22,RHBatch01New256Block37Checks.row23,RHBatch01New256Block37Checks.row24,RHBatch01New256Block37Checks.row25,RHBatch01New256Block37Checks.row26,RHBatch01New256Block37Checks.row27,RHBatch01New256Block37Checks.row28,RHBatch01New256Block37Checks.row29,RHBatch01New256Block37Checks.row30,RHBatch01New256Block37Checks.row31]
#print axioms solution
