-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block24
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:41:59.643415+00:00
-- url     : https://prove2.me/submissions/c1ebbae5-4be2-44cd-87d3-91e9e7d0333d

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block24Checks
theorem row00 : RHBatch01New256CompactReference.checked (768+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (768+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (768+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (768+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (768+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (768+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (768+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (768+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (768+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (768+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (768+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (768+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (768+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (768+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (768+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (768+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (768+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (768+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (768+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (768+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (768+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (768+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (768+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (768+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (768+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (768+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (768+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (768+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (768+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (768+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (768+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (768+31)=true := by decide +kernel
end RHBatch01New256Block24Checks

theorem solution : RHBatch01New256CompactReference.block 768 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block24Checks.row00,RHBatch01New256Block24Checks.row01,RHBatch01New256Block24Checks.row02,RHBatch01New256Block24Checks.row03,RHBatch01New256Block24Checks.row04,RHBatch01New256Block24Checks.row05,RHBatch01New256Block24Checks.row06,RHBatch01New256Block24Checks.row07,RHBatch01New256Block24Checks.row08,RHBatch01New256Block24Checks.row09,RHBatch01New256Block24Checks.row10,RHBatch01New256Block24Checks.row11,RHBatch01New256Block24Checks.row12,RHBatch01New256Block24Checks.row13,RHBatch01New256Block24Checks.row14,RHBatch01New256Block24Checks.row15,RHBatch01New256Block24Checks.row16,RHBatch01New256Block24Checks.row17,RHBatch01New256Block24Checks.row18,RHBatch01New256Block24Checks.row19,RHBatch01New256Block24Checks.row20,RHBatch01New256Block24Checks.row21,RHBatch01New256Block24Checks.row22,RHBatch01New256Block24Checks.row23,RHBatch01New256Block24Checks.row24,RHBatch01New256Block24Checks.row25,RHBatch01New256Block24Checks.row26,RHBatch01New256Block24Checks.row27,RHBatch01New256Block24Checks.row28,RHBatch01New256Block24Checks.row29,RHBatch01New256Block24Checks.row30,RHBatch01New256Block24Checks.row31]
#print axioms solution
