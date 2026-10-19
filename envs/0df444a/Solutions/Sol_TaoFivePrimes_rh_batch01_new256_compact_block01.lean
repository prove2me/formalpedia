-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block01
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:30:50.831846+00:00
-- url     : https://prove2.me/submissions/f4f87d50-f2fc-41a3-beb1-c525107047da

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block01Checks
theorem row00 : RHBatch01New256CompactReference.checked (32+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (32+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (32+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (32+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (32+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (32+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (32+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (32+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (32+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (32+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (32+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (32+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (32+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (32+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (32+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (32+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (32+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (32+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (32+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (32+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (32+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (32+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (32+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (32+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (32+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (32+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (32+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (32+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (32+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (32+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (32+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (32+31)=true := by decide +kernel
end RHBatch01New256Block01Checks

theorem solution : RHBatch01New256CompactReference.block 32 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block01Checks.row00,RHBatch01New256Block01Checks.row01,RHBatch01New256Block01Checks.row02,RHBatch01New256Block01Checks.row03,RHBatch01New256Block01Checks.row04,RHBatch01New256Block01Checks.row05,RHBatch01New256Block01Checks.row06,RHBatch01New256Block01Checks.row07,RHBatch01New256Block01Checks.row08,RHBatch01New256Block01Checks.row09,RHBatch01New256Block01Checks.row10,RHBatch01New256Block01Checks.row11,RHBatch01New256Block01Checks.row12,RHBatch01New256Block01Checks.row13,RHBatch01New256Block01Checks.row14,RHBatch01New256Block01Checks.row15,RHBatch01New256Block01Checks.row16,RHBatch01New256Block01Checks.row17,RHBatch01New256Block01Checks.row18,RHBatch01New256Block01Checks.row19,RHBatch01New256Block01Checks.row20,RHBatch01New256Block01Checks.row21,RHBatch01New256Block01Checks.row22,RHBatch01New256Block01Checks.row23,RHBatch01New256Block01Checks.row24,RHBatch01New256Block01Checks.row25,RHBatch01New256Block01Checks.row26,RHBatch01New256Block01Checks.row27,RHBatch01New256Block01Checks.row28,RHBatch01New256Block01Checks.row29,RHBatch01New256Block01Checks.row30,RHBatch01New256Block01Checks.row31]
#print axioms solution
