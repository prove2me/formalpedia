-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block40
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:18:55.500102+00:00
-- url     : https://prove2.me/submissions/d568e2d9-a071-45f9-b05b-9bc944cb7841

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block40Checks
theorem row00 : RHBatch01New256CompactReference.checked (1280+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1280+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1280+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1280+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1280+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1280+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1280+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1280+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1280+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1280+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1280+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1280+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1280+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1280+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1280+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1280+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1280+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1280+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1280+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1280+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1280+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1280+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1280+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1280+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1280+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1280+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1280+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1280+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1280+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1280+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1280+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1280+31)=true := by decide +kernel
end RHBatch01New256Block40Checks

theorem solution : RHBatch01New256CompactReference.block 1280 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block40Checks.row00,RHBatch01New256Block40Checks.row01,RHBatch01New256Block40Checks.row02,RHBatch01New256Block40Checks.row03,RHBatch01New256Block40Checks.row04,RHBatch01New256Block40Checks.row05,RHBatch01New256Block40Checks.row06,RHBatch01New256Block40Checks.row07,RHBatch01New256Block40Checks.row08,RHBatch01New256Block40Checks.row09,RHBatch01New256Block40Checks.row10,RHBatch01New256Block40Checks.row11,RHBatch01New256Block40Checks.row12,RHBatch01New256Block40Checks.row13,RHBatch01New256Block40Checks.row14,RHBatch01New256Block40Checks.row15,RHBatch01New256Block40Checks.row16,RHBatch01New256Block40Checks.row17,RHBatch01New256Block40Checks.row18,RHBatch01New256Block40Checks.row19,RHBatch01New256Block40Checks.row20,RHBatch01New256Block40Checks.row21,RHBatch01New256Block40Checks.row22,RHBatch01New256Block40Checks.row23,RHBatch01New256Block40Checks.row24,RHBatch01New256Block40Checks.row25,RHBatch01New256Block40Checks.row26,RHBatch01New256Block40Checks.row27,RHBatch01New256Block40Checks.row28,RHBatch01New256Block40Checks.row29,RHBatch01New256Block40Checks.row30,RHBatch01New256Block40Checks.row31]
#print axioms solution
