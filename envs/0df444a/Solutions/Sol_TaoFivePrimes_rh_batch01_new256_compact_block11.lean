-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block11
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:56:50.833988+00:00
-- url     : https://prove2.me/submissions/4f351e52-dc61-4b1e-9506-e3ce8c5b050f

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block11Checks
theorem row00 : RHBatch01New256CompactReference.checked (352+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (352+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (352+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (352+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (352+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (352+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (352+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (352+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (352+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (352+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (352+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (352+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (352+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (352+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (352+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (352+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (352+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (352+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (352+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (352+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (352+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (352+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (352+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (352+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (352+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (352+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (352+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (352+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (352+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (352+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (352+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (352+31)=true := by decide +kernel
end RHBatch01New256Block11Checks

theorem solution : RHBatch01New256CompactReference.block 352 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block11Checks.row00,RHBatch01New256Block11Checks.row01,RHBatch01New256Block11Checks.row02,RHBatch01New256Block11Checks.row03,RHBatch01New256Block11Checks.row04,RHBatch01New256Block11Checks.row05,RHBatch01New256Block11Checks.row06,RHBatch01New256Block11Checks.row07,RHBatch01New256Block11Checks.row08,RHBatch01New256Block11Checks.row09,RHBatch01New256Block11Checks.row10,RHBatch01New256Block11Checks.row11,RHBatch01New256Block11Checks.row12,RHBatch01New256Block11Checks.row13,RHBatch01New256Block11Checks.row14,RHBatch01New256Block11Checks.row15,RHBatch01New256Block11Checks.row16,RHBatch01New256Block11Checks.row17,RHBatch01New256Block11Checks.row18,RHBatch01New256Block11Checks.row19,RHBatch01New256Block11Checks.row20,RHBatch01New256Block11Checks.row21,RHBatch01New256Block11Checks.row22,RHBatch01New256Block11Checks.row23,RHBatch01New256Block11Checks.row24,RHBatch01New256Block11Checks.row25,RHBatch01New256Block11Checks.row26,RHBatch01New256Block11Checks.row27,RHBatch01New256Block11Checks.row28,RHBatch01New256Block11Checks.row29,RHBatch01New256Block11Checks.row30,RHBatch01New256Block11Checks.row31]
#print axioms solution
