-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block53
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:32:37.794499+00:00
-- url     : https://prove2.me/submissions/d11eb70d-f201-4400-a10b-bbe53930ea55

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block53Checks
theorem row00 : RHBatch01New256CompactReference.checked (1696+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1696+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1696+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1696+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1696+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1696+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1696+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1696+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1696+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1696+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1696+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1696+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1696+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1696+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1696+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1696+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1696+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1696+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1696+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1696+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1696+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1696+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1696+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1696+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1696+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1696+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1696+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1696+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1696+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1696+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1696+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1696+31)=true := by decide +kernel
end RHBatch01New256Block53Checks

theorem solution : RHBatch01New256CompactReference.block 1696 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block53Checks.row00,RHBatch01New256Block53Checks.row01,RHBatch01New256Block53Checks.row02,RHBatch01New256Block53Checks.row03,RHBatch01New256Block53Checks.row04,RHBatch01New256Block53Checks.row05,RHBatch01New256Block53Checks.row06,RHBatch01New256Block53Checks.row07,RHBatch01New256Block53Checks.row08,RHBatch01New256Block53Checks.row09,RHBatch01New256Block53Checks.row10,RHBatch01New256Block53Checks.row11,RHBatch01New256Block53Checks.row12,RHBatch01New256Block53Checks.row13,RHBatch01New256Block53Checks.row14,RHBatch01New256Block53Checks.row15,RHBatch01New256Block53Checks.row16,RHBatch01New256Block53Checks.row17,RHBatch01New256Block53Checks.row18,RHBatch01New256Block53Checks.row19,RHBatch01New256Block53Checks.row20,RHBatch01New256Block53Checks.row21,RHBatch01New256Block53Checks.row22,RHBatch01New256Block53Checks.row23,RHBatch01New256Block53Checks.row24,RHBatch01New256Block53Checks.row25,RHBatch01New256Block53Checks.row26,RHBatch01New256Block53Checks.row27,RHBatch01New256Block53Checks.row28,RHBatch01New256Block53Checks.row29,RHBatch01New256Block53Checks.row30,RHBatch01New256Block53Checks.row31]
#print axioms solution
