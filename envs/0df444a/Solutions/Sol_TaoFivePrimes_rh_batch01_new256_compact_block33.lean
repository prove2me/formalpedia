-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block33
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:05:55.353119+00:00
-- url     : https://prove2.me/submissions/3dad1039-4733-4ad4-9faf-5f5924d5ea71

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block33Checks
theorem row00 : RHBatch01New256CompactReference.checked (1056+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1056+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1056+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1056+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1056+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1056+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1056+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1056+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1056+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1056+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1056+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1056+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1056+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1056+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1056+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1056+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1056+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1056+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1056+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1056+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1056+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1056+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1056+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1056+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1056+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1056+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1056+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1056+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1056+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1056+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1056+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1056+31)=true := by decide +kernel
end RHBatch01New256Block33Checks

theorem solution : RHBatch01New256CompactReference.block 1056 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block33Checks.row00,RHBatch01New256Block33Checks.row01,RHBatch01New256Block33Checks.row02,RHBatch01New256Block33Checks.row03,RHBatch01New256Block33Checks.row04,RHBatch01New256Block33Checks.row05,RHBatch01New256Block33Checks.row06,RHBatch01New256Block33Checks.row07,RHBatch01New256Block33Checks.row08,RHBatch01New256Block33Checks.row09,RHBatch01New256Block33Checks.row10,RHBatch01New256Block33Checks.row11,RHBatch01New256Block33Checks.row12,RHBatch01New256Block33Checks.row13,RHBatch01New256Block33Checks.row14,RHBatch01New256Block33Checks.row15,RHBatch01New256Block33Checks.row16,RHBatch01New256Block33Checks.row17,RHBatch01New256Block33Checks.row18,RHBatch01New256Block33Checks.row19,RHBatch01New256Block33Checks.row20,RHBatch01New256Block33Checks.row21,RHBatch01New256Block33Checks.row22,RHBatch01New256Block33Checks.row23,RHBatch01New256Block33Checks.row24,RHBatch01New256Block33Checks.row25,RHBatch01New256Block33Checks.row26,RHBatch01New256Block33Checks.row27,RHBatch01New256Block33Checks.row28,RHBatch01New256Block33Checks.row29,RHBatch01New256Block33Checks.row30,RHBatch01New256Block33Checks.row31]
#print axioms solution
