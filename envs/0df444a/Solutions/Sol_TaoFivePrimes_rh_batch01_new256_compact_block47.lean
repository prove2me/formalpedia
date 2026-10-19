-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block47
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:28:53.205004+00:00
-- url     : https://prove2.me/submissions/2ef938d3-f890-4d1d-8667-802fb9d70062

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block47Checks
theorem row00 : RHBatch01New256CompactReference.checked (1504+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1504+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1504+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1504+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1504+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1504+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1504+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1504+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1504+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1504+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1504+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1504+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1504+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1504+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1504+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1504+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1504+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1504+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1504+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1504+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1504+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1504+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1504+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1504+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1504+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1504+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1504+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1504+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1504+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1504+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1504+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1504+31)=true := by decide +kernel
end RHBatch01New256Block47Checks

theorem solution : RHBatch01New256CompactReference.block 1504 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block47Checks.row00,RHBatch01New256Block47Checks.row01,RHBatch01New256Block47Checks.row02,RHBatch01New256Block47Checks.row03,RHBatch01New256Block47Checks.row04,RHBatch01New256Block47Checks.row05,RHBatch01New256Block47Checks.row06,RHBatch01New256Block47Checks.row07,RHBatch01New256Block47Checks.row08,RHBatch01New256Block47Checks.row09,RHBatch01New256Block47Checks.row10,RHBatch01New256Block47Checks.row11,RHBatch01New256Block47Checks.row12,RHBatch01New256Block47Checks.row13,RHBatch01New256Block47Checks.row14,RHBatch01New256Block47Checks.row15,RHBatch01New256Block47Checks.row16,RHBatch01New256Block47Checks.row17,RHBatch01New256Block47Checks.row18,RHBatch01New256Block47Checks.row19,RHBatch01New256Block47Checks.row20,RHBatch01New256Block47Checks.row21,RHBatch01New256Block47Checks.row22,RHBatch01New256Block47Checks.row23,RHBatch01New256Block47Checks.row24,RHBatch01New256Block47Checks.row25,RHBatch01New256Block47Checks.row26,RHBatch01New256Block47Checks.row27,RHBatch01New256Block47Checks.row28,RHBatch01New256Block47Checks.row29,RHBatch01New256Block47Checks.row30,RHBatch01New256Block47Checks.row31]
#print axioms solution
