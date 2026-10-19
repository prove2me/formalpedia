-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block44
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:22:13.085411+00:00
-- url     : https://prove2.me/submissions/e0878d12-cc14-4dc4-8130-038ee69624ba

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block44Checks
theorem row00 : RHBatch01New256CompactReference.checked (1408+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1408+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1408+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1408+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1408+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1408+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1408+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1408+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1408+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1408+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1408+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1408+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1408+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1408+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1408+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1408+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1408+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1408+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1408+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1408+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1408+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1408+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1408+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1408+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1408+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1408+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1408+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1408+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1408+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1408+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1408+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1408+31)=true := by decide +kernel
end RHBatch01New256Block44Checks

theorem solution : RHBatch01New256CompactReference.block 1408 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block44Checks.row00,RHBatch01New256Block44Checks.row01,RHBatch01New256Block44Checks.row02,RHBatch01New256Block44Checks.row03,RHBatch01New256Block44Checks.row04,RHBatch01New256Block44Checks.row05,RHBatch01New256Block44Checks.row06,RHBatch01New256Block44Checks.row07,RHBatch01New256Block44Checks.row08,RHBatch01New256Block44Checks.row09,RHBatch01New256Block44Checks.row10,RHBatch01New256Block44Checks.row11,RHBatch01New256Block44Checks.row12,RHBatch01New256Block44Checks.row13,RHBatch01New256Block44Checks.row14,RHBatch01New256Block44Checks.row15,RHBatch01New256Block44Checks.row16,RHBatch01New256Block44Checks.row17,RHBatch01New256Block44Checks.row18,RHBatch01New256Block44Checks.row19,RHBatch01New256Block44Checks.row20,RHBatch01New256Block44Checks.row21,RHBatch01New256Block44Checks.row22,RHBatch01New256Block44Checks.row23,RHBatch01New256Block44Checks.row24,RHBatch01New256Block44Checks.row25,RHBatch01New256Block44Checks.row26,RHBatch01New256Block44Checks.row27,RHBatch01New256Block44Checks.row28,RHBatch01New256Block44Checks.row29,RHBatch01New256Block44Checks.row30,RHBatch01New256Block44Checks.row31]
#print axioms solution
