-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block41
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:20:26.181746+00:00
-- url     : https://prove2.me/submissions/b702e435-4190-40e8-b091-f156b7177dfd

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block41Checks
theorem row00 : RHBatch01New256CompactReference.checked (1312+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1312+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1312+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1312+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1312+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1312+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1312+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1312+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1312+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1312+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1312+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1312+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1312+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1312+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1312+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1312+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1312+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1312+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1312+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1312+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1312+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1312+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1312+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1312+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1312+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1312+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1312+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1312+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1312+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1312+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1312+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1312+31)=true := by decide +kernel
end RHBatch01New256Block41Checks

theorem solution : RHBatch01New256CompactReference.block 1312 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block41Checks.row00,RHBatch01New256Block41Checks.row01,RHBatch01New256Block41Checks.row02,RHBatch01New256Block41Checks.row03,RHBatch01New256Block41Checks.row04,RHBatch01New256Block41Checks.row05,RHBatch01New256Block41Checks.row06,RHBatch01New256Block41Checks.row07,RHBatch01New256Block41Checks.row08,RHBatch01New256Block41Checks.row09,RHBatch01New256Block41Checks.row10,RHBatch01New256Block41Checks.row11,RHBatch01New256Block41Checks.row12,RHBatch01New256Block41Checks.row13,RHBatch01New256Block41Checks.row14,RHBatch01New256Block41Checks.row15,RHBatch01New256Block41Checks.row16,RHBatch01New256Block41Checks.row17,RHBatch01New256Block41Checks.row18,RHBatch01New256Block41Checks.row19,RHBatch01New256Block41Checks.row20,RHBatch01New256Block41Checks.row21,RHBatch01New256Block41Checks.row22,RHBatch01New256Block41Checks.row23,RHBatch01New256Block41Checks.row24,RHBatch01New256Block41Checks.row25,RHBatch01New256Block41Checks.row26,RHBatch01New256Block41Checks.row27,RHBatch01New256Block41Checks.row28,RHBatch01New256Block41Checks.row29,RHBatch01New256Block41Checks.row30,RHBatch01New256Block41Checks.row31]
#print axioms solution
