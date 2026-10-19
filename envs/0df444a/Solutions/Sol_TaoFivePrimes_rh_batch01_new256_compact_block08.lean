-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:41:39.820549+00:00
-- url     : https://prove2.me/submissions/15dbb173-a273-49d0-bf48-a26f2b02b299

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block08Checks
theorem row00 : RHBatch01New256CompactReference.checked (256+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (256+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (256+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (256+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (256+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (256+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (256+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (256+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (256+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (256+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (256+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (256+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (256+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (256+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (256+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (256+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (256+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (256+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (256+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (256+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (256+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (256+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (256+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (256+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (256+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (256+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (256+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (256+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (256+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (256+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (256+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (256+31)=true := by decide +kernel
end RHBatch01New256Block08Checks

theorem solution : RHBatch01New256CompactReference.block 256 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block08Checks.row00,RHBatch01New256Block08Checks.row01,RHBatch01New256Block08Checks.row02,RHBatch01New256Block08Checks.row03,RHBatch01New256Block08Checks.row04,RHBatch01New256Block08Checks.row05,RHBatch01New256Block08Checks.row06,RHBatch01New256Block08Checks.row07,RHBatch01New256Block08Checks.row08,RHBatch01New256Block08Checks.row09,RHBatch01New256Block08Checks.row10,RHBatch01New256Block08Checks.row11,RHBatch01New256Block08Checks.row12,RHBatch01New256Block08Checks.row13,RHBatch01New256Block08Checks.row14,RHBatch01New256Block08Checks.row15,RHBatch01New256Block08Checks.row16,RHBatch01New256Block08Checks.row17,RHBatch01New256Block08Checks.row18,RHBatch01New256Block08Checks.row19,RHBatch01New256Block08Checks.row20,RHBatch01New256Block08Checks.row21,RHBatch01New256Block08Checks.row22,RHBatch01New256Block08Checks.row23,RHBatch01New256Block08Checks.row24,RHBatch01New256Block08Checks.row25,RHBatch01New256Block08Checks.row26,RHBatch01New256Block08Checks.row27,RHBatch01New256Block08Checks.row28,RHBatch01New256Block08Checks.row29,RHBatch01New256Block08Checks.row30,RHBatch01New256Block08Checks.row31]
#print axioms solution
