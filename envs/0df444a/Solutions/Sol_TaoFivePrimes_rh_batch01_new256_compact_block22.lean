-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block22
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T14:53:50.724767+00:00
-- url     : https://prove2.me/submissions/a302d3bc-6fb6-4e98-ba01-0e03c40ed6e8

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block22Checks
theorem row00 : RHBatch01New256CompactReference.checked (704+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (704+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (704+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (704+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (704+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (704+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (704+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (704+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (704+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (704+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (704+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (704+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (704+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (704+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (704+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (704+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (704+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (704+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (704+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (704+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (704+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (704+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (704+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (704+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (704+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (704+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (704+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (704+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (704+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (704+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (704+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (704+31)=true := by decide +kernel
end RHBatch01New256Block22Checks

theorem solution : RHBatch01New256CompactReference.block 704 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block22Checks.row00,RHBatch01New256Block22Checks.row01,RHBatch01New256Block22Checks.row02,RHBatch01New256Block22Checks.row03,RHBatch01New256Block22Checks.row04,RHBatch01New256Block22Checks.row05,RHBatch01New256Block22Checks.row06,RHBatch01New256Block22Checks.row07,RHBatch01New256Block22Checks.row08,RHBatch01New256Block22Checks.row09,RHBatch01New256Block22Checks.row10,RHBatch01New256Block22Checks.row11,RHBatch01New256Block22Checks.row12,RHBatch01New256Block22Checks.row13,RHBatch01New256Block22Checks.row14,RHBatch01New256Block22Checks.row15,RHBatch01New256Block22Checks.row16,RHBatch01New256Block22Checks.row17,RHBatch01New256Block22Checks.row18,RHBatch01New256Block22Checks.row19,RHBatch01New256Block22Checks.row20,RHBatch01New256Block22Checks.row21,RHBatch01New256Block22Checks.row22,RHBatch01New256Block22Checks.row23,RHBatch01New256Block22Checks.row24,RHBatch01New256Block22Checks.row25,RHBatch01New256Block22Checks.row26,RHBatch01New256Block22Checks.row27,RHBatch01New256Block22Checks.row28,RHBatch01New256Block22Checks.row29,RHBatch01New256Block22Checks.row30,RHBatch01New256Block22Checks.row31]
#print axioms solution
