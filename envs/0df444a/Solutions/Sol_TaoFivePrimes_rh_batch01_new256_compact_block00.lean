-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block00
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:32:41.80028+00:00
-- url     : https://prove2.me/submissions/3b35dbc2-a946-4d1b-bf0a-5acf754625fb

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block00Checks
theorem row00 : RHBatch01New256CompactReference.checked (0+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (0+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (0+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (0+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (0+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (0+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (0+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (0+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (0+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (0+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (0+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (0+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (0+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (0+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (0+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (0+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (0+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (0+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (0+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (0+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (0+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (0+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (0+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (0+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (0+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (0+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (0+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (0+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (0+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (0+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (0+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (0+31)=true := by decide +kernel
end RHBatch01New256Block00Checks

theorem solution : RHBatch01New256CompactReference.block 0 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block00Checks.row00,RHBatch01New256Block00Checks.row01,RHBatch01New256Block00Checks.row02,RHBatch01New256Block00Checks.row03,RHBatch01New256Block00Checks.row04,RHBatch01New256Block00Checks.row05,RHBatch01New256Block00Checks.row06,RHBatch01New256Block00Checks.row07,RHBatch01New256Block00Checks.row08,RHBatch01New256Block00Checks.row09,RHBatch01New256Block00Checks.row10,RHBatch01New256Block00Checks.row11,RHBatch01New256Block00Checks.row12,RHBatch01New256Block00Checks.row13,RHBatch01New256Block00Checks.row14,RHBatch01New256Block00Checks.row15,RHBatch01New256Block00Checks.row16,RHBatch01New256Block00Checks.row17,RHBatch01New256Block00Checks.row18,RHBatch01New256Block00Checks.row19,RHBatch01New256Block00Checks.row20,RHBatch01New256Block00Checks.row21,RHBatch01New256Block00Checks.row22,RHBatch01New256Block00Checks.row23,RHBatch01New256Block00Checks.row24,RHBatch01New256Block00Checks.row25,RHBatch01New256Block00Checks.row26,RHBatch01New256Block00Checks.row27,RHBatch01New256Block00Checks.row28,RHBatch01New256Block00Checks.row29,RHBatch01New256Block00Checks.row30,RHBatch01New256Block00Checks.row31]
#print axioms solution
