-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block36
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:11:27.648344+00:00
-- url     : https://prove2.me/submissions/2842ad78-dd85-47c6-94bc-ed7577e34d3d

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block36Checks
theorem row00 : RHBatch01New256CompactReference.checked (1152+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1152+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1152+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1152+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1152+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1152+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1152+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1152+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1152+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1152+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1152+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1152+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1152+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1152+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1152+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1152+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1152+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1152+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1152+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1152+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1152+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1152+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1152+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1152+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1152+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1152+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1152+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1152+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1152+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1152+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1152+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1152+31)=true := by decide +kernel
end RHBatch01New256Block36Checks

theorem solution : RHBatch01New256CompactReference.block 1152 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block36Checks.row00,RHBatch01New256Block36Checks.row01,RHBatch01New256Block36Checks.row02,RHBatch01New256Block36Checks.row03,RHBatch01New256Block36Checks.row04,RHBatch01New256Block36Checks.row05,RHBatch01New256Block36Checks.row06,RHBatch01New256Block36Checks.row07,RHBatch01New256Block36Checks.row08,RHBatch01New256Block36Checks.row09,RHBatch01New256Block36Checks.row10,RHBatch01New256Block36Checks.row11,RHBatch01New256Block36Checks.row12,RHBatch01New256Block36Checks.row13,RHBatch01New256Block36Checks.row14,RHBatch01New256Block36Checks.row15,RHBatch01New256Block36Checks.row16,RHBatch01New256Block36Checks.row17,RHBatch01New256Block36Checks.row18,RHBatch01New256Block36Checks.row19,RHBatch01New256Block36Checks.row20,RHBatch01New256Block36Checks.row21,RHBatch01New256Block36Checks.row22,RHBatch01New256Block36Checks.row23,RHBatch01New256Block36Checks.row24,RHBatch01New256Block36Checks.row25,RHBatch01New256Block36Checks.row26,RHBatch01New256Block36Checks.row27,RHBatch01New256Block36Checks.row28,RHBatch01New256Block36Checks.row29,RHBatch01New256Block36Checks.row30,RHBatch01New256Block36Checks.row31]
#print axioms solution
