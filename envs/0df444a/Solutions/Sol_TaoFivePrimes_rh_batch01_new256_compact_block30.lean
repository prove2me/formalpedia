-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block30
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T16:12:06.527816+00:00
-- url     : https://prove2.me/submissions/c471473a-b455-4721-bcd8-a9174a9d072e

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block30Checks
theorem row00 : RHBatch01New256CompactReference.checked (960+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (960+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (960+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (960+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (960+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (960+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (960+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (960+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (960+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (960+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (960+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (960+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (960+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (960+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (960+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (960+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (960+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (960+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (960+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (960+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (960+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (960+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (960+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (960+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (960+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (960+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (960+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (960+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (960+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (960+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (960+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (960+31)=true := by decide +kernel
end RHBatch01New256Block30Checks

theorem solution : RHBatch01New256CompactReference.block 960 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block30Checks.row00,RHBatch01New256Block30Checks.row01,RHBatch01New256Block30Checks.row02,RHBatch01New256Block30Checks.row03,RHBatch01New256Block30Checks.row04,RHBatch01New256Block30Checks.row05,RHBatch01New256Block30Checks.row06,RHBatch01New256Block30Checks.row07,RHBatch01New256Block30Checks.row08,RHBatch01New256Block30Checks.row09,RHBatch01New256Block30Checks.row10,RHBatch01New256Block30Checks.row11,RHBatch01New256Block30Checks.row12,RHBatch01New256Block30Checks.row13,RHBatch01New256Block30Checks.row14,RHBatch01New256Block30Checks.row15,RHBatch01New256Block30Checks.row16,RHBatch01New256Block30Checks.row17,RHBatch01New256Block30Checks.row18,RHBatch01New256Block30Checks.row19,RHBatch01New256Block30Checks.row20,RHBatch01New256Block30Checks.row21,RHBatch01New256Block30Checks.row22,RHBatch01New256Block30Checks.row23,RHBatch01New256Block30Checks.row24,RHBatch01New256Block30Checks.row25,RHBatch01New256Block30Checks.row26,RHBatch01New256Block30Checks.row27,RHBatch01New256Block30Checks.row28,RHBatch01New256Block30Checks.row29,RHBatch01New256Block30Checks.row30,RHBatch01New256Block30Checks.row31]
#print axioms solution
