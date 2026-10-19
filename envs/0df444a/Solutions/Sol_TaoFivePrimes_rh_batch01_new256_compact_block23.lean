-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block23
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T15:34:56.158344+00:00
-- url     : https://prove2.me/submissions/67c42ad9-65c1-49ce-b7ed-260f58b1cfcb

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block23Checks
theorem row00 : RHBatch01New256CompactReference.checked (736+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (736+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (736+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (736+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (736+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (736+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (736+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (736+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (736+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (736+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (736+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (736+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (736+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (736+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (736+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (736+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (736+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (736+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (736+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (736+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (736+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (736+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (736+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (736+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (736+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (736+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (736+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (736+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (736+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (736+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (736+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (736+31)=true := by decide +kernel
end RHBatch01New256Block23Checks

theorem solution : RHBatch01New256CompactReference.block 736 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block23Checks.row00,RHBatch01New256Block23Checks.row01,RHBatch01New256Block23Checks.row02,RHBatch01New256Block23Checks.row03,RHBatch01New256Block23Checks.row04,RHBatch01New256Block23Checks.row05,RHBatch01New256Block23Checks.row06,RHBatch01New256Block23Checks.row07,RHBatch01New256Block23Checks.row08,RHBatch01New256Block23Checks.row09,RHBatch01New256Block23Checks.row10,RHBatch01New256Block23Checks.row11,RHBatch01New256Block23Checks.row12,RHBatch01New256Block23Checks.row13,RHBatch01New256Block23Checks.row14,RHBatch01New256Block23Checks.row15,RHBatch01New256Block23Checks.row16,RHBatch01New256Block23Checks.row17,RHBatch01New256Block23Checks.row18,RHBatch01New256Block23Checks.row19,RHBatch01New256Block23Checks.row20,RHBatch01New256Block23Checks.row21,RHBatch01New256Block23Checks.row22,RHBatch01New256Block23Checks.row23,RHBatch01New256Block23Checks.row24,RHBatch01New256Block23Checks.row25,RHBatch01New256Block23Checks.row26,RHBatch01New256Block23Checks.row27,RHBatch01New256Block23Checks.row28,RHBatch01New256Block23Checks.row29,RHBatch01New256Block23Checks.row30,RHBatch01New256Block23Checks.row31]
#print axioms solution
