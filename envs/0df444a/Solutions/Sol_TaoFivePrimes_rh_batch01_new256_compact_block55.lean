-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block55
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:34:29.610693+00:00
-- url     : https://prove2.me/submissions/ac9183ba-c8d5-4277-8011-7e84b2b08748

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block55Checks
theorem row00 : RHBatch01New256CompactReference.checked (1760+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1760+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1760+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1760+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1760+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1760+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1760+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1760+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1760+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1760+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1760+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1760+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1760+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1760+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1760+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1760+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1760+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1760+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1760+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1760+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1760+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1760+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1760+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1760+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1760+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1760+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1760+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1760+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1760+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1760+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1760+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1760+31)=true := by decide +kernel
end RHBatch01New256Block55Checks

theorem solution : RHBatch01New256CompactReference.block 1760 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block55Checks.row00,RHBatch01New256Block55Checks.row01,RHBatch01New256Block55Checks.row02,RHBatch01New256Block55Checks.row03,RHBatch01New256Block55Checks.row04,RHBatch01New256Block55Checks.row05,RHBatch01New256Block55Checks.row06,RHBatch01New256Block55Checks.row07,RHBatch01New256Block55Checks.row08,RHBatch01New256Block55Checks.row09,RHBatch01New256Block55Checks.row10,RHBatch01New256Block55Checks.row11,RHBatch01New256Block55Checks.row12,RHBatch01New256Block55Checks.row13,RHBatch01New256Block55Checks.row14,RHBatch01New256Block55Checks.row15,RHBatch01New256Block55Checks.row16,RHBatch01New256Block55Checks.row17,RHBatch01New256Block55Checks.row18,RHBatch01New256Block55Checks.row19,RHBatch01New256Block55Checks.row20,RHBatch01New256Block55Checks.row21,RHBatch01New256Block55Checks.row22,RHBatch01New256Block55Checks.row23,RHBatch01New256Block55Checks.row24,RHBatch01New256Block55Checks.row25,RHBatch01New256Block55Checks.row26,RHBatch01New256Block55Checks.row27,RHBatch01New256Block55Checks.row28,RHBatch01New256Block55Checks.row29,RHBatch01New256Block55Checks.row30,RHBatch01New256Block55Checks.row31]
#print axioms solution
