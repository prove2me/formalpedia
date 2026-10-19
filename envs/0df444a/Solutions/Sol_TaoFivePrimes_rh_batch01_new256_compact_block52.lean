-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block52
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:32:09.989222+00:00
-- url     : https://prove2.me/submissions/2c0aca38-28db-4040-896c-cd99981eca5b

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block52Checks
theorem row00 : RHBatch01New256CompactReference.checked (1664+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1664+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1664+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1664+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1664+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1664+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1664+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1664+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1664+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1664+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1664+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1664+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1664+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1664+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1664+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1664+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1664+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1664+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1664+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1664+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1664+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1664+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1664+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1664+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1664+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1664+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1664+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1664+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1664+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1664+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1664+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1664+31)=true := by decide +kernel
end RHBatch01New256Block52Checks

theorem solution : RHBatch01New256CompactReference.block 1664 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block52Checks.row00,RHBatch01New256Block52Checks.row01,RHBatch01New256Block52Checks.row02,RHBatch01New256Block52Checks.row03,RHBatch01New256Block52Checks.row04,RHBatch01New256Block52Checks.row05,RHBatch01New256Block52Checks.row06,RHBatch01New256Block52Checks.row07,RHBatch01New256Block52Checks.row08,RHBatch01New256Block52Checks.row09,RHBatch01New256Block52Checks.row10,RHBatch01New256Block52Checks.row11,RHBatch01New256Block52Checks.row12,RHBatch01New256Block52Checks.row13,RHBatch01New256Block52Checks.row14,RHBatch01New256Block52Checks.row15,RHBatch01New256Block52Checks.row16,RHBatch01New256Block52Checks.row17,RHBatch01New256Block52Checks.row18,RHBatch01New256Block52Checks.row19,RHBatch01New256Block52Checks.row20,RHBatch01New256Block52Checks.row21,RHBatch01New256Block52Checks.row22,RHBatch01New256Block52Checks.row23,RHBatch01New256Block52Checks.row24,RHBatch01New256Block52Checks.row25,RHBatch01New256Block52Checks.row26,RHBatch01New256Block52Checks.row27,RHBatch01New256Block52Checks.row28,RHBatch01New256Block52Checks.row29,RHBatch01New256Block52Checks.row30,RHBatch01New256Block52Checks.row31]
#print axioms solution
