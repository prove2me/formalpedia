-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block48
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:30:17.748115+00:00
-- url     : https://prove2.me/submissions/a342b6f4-1eca-4813-b365-a217cc64b75d

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block48Checks
theorem row00 : RHBatch01New256CompactReference.checked (1536+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1536+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1536+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1536+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1536+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1536+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1536+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1536+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1536+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1536+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1536+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1536+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1536+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1536+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1536+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1536+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1536+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1536+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1536+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1536+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1536+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1536+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1536+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1536+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1536+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1536+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1536+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1536+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1536+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1536+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1536+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1536+31)=true := by decide +kernel
end RHBatch01New256Block48Checks

theorem solution : RHBatch01New256CompactReference.block 1536 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block48Checks.row00,RHBatch01New256Block48Checks.row01,RHBatch01New256Block48Checks.row02,RHBatch01New256Block48Checks.row03,RHBatch01New256Block48Checks.row04,RHBatch01New256Block48Checks.row05,RHBatch01New256Block48Checks.row06,RHBatch01New256Block48Checks.row07,RHBatch01New256Block48Checks.row08,RHBatch01New256Block48Checks.row09,RHBatch01New256Block48Checks.row10,RHBatch01New256Block48Checks.row11,RHBatch01New256Block48Checks.row12,RHBatch01New256Block48Checks.row13,RHBatch01New256Block48Checks.row14,RHBatch01New256Block48Checks.row15,RHBatch01New256Block48Checks.row16,RHBatch01New256Block48Checks.row17,RHBatch01New256Block48Checks.row18,RHBatch01New256Block48Checks.row19,RHBatch01New256Block48Checks.row20,RHBatch01New256Block48Checks.row21,RHBatch01New256Block48Checks.row22,RHBatch01New256Block48Checks.row23,RHBatch01New256Block48Checks.row24,RHBatch01New256Block48Checks.row25,RHBatch01New256Block48Checks.row26,RHBatch01New256Block48Checks.row27,RHBatch01New256Block48Checks.row28,RHBatch01New256Block48Checks.row29,RHBatch01New256Block48Checks.row30,RHBatch01New256Block48Checks.row31]
#print axioms solution
