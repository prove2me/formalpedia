-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block38
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:15:33.730853+00:00
-- url     : https://prove2.me/submissions/510fcf1e-40d7-4722-ba63-5444f6410e46

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block38Checks
theorem row00 : RHBatch01New256CompactReference.checked (1216+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (1216+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (1216+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (1216+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (1216+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (1216+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (1216+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (1216+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (1216+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (1216+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (1216+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (1216+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (1216+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (1216+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (1216+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (1216+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (1216+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (1216+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (1216+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (1216+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (1216+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (1216+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (1216+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (1216+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (1216+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (1216+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (1216+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (1216+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (1216+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (1216+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (1216+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (1216+31)=true := by decide +kernel
end RHBatch01New256Block38Checks

theorem solution : RHBatch01New256CompactReference.block 1216 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block38Checks.row00,RHBatch01New256Block38Checks.row01,RHBatch01New256Block38Checks.row02,RHBatch01New256Block38Checks.row03,RHBatch01New256Block38Checks.row04,RHBatch01New256Block38Checks.row05,RHBatch01New256Block38Checks.row06,RHBatch01New256Block38Checks.row07,RHBatch01New256Block38Checks.row08,RHBatch01New256Block38Checks.row09,RHBatch01New256Block38Checks.row10,RHBatch01New256Block38Checks.row11,RHBatch01New256Block38Checks.row12,RHBatch01New256Block38Checks.row13,RHBatch01New256Block38Checks.row14,RHBatch01New256Block38Checks.row15,RHBatch01New256Block38Checks.row16,RHBatch01New256Block38Checks.row17,RHBatch01New256Block38Checks.row18,RHBatch01New256Block38Checks.row19,RHBatch01New256Block38Checks.row20,RHBatch01New256Block38Checks.row21,RHBatch01New256Block38Checks.row22,RHBatch01New256Block38Checks.row23,RHBatch01New256Block38Checks.row24,RHBatch01New256Block38Checks.row25,RHBatch01New256Block38Checks.row26,RHBatch01New256Block38Checks.row27,RHBatch01New256Block38Checks.row28,RHBatch01New256Block38Checks.row29,RHBatch01New256Block38Checks.row30,RHBatch01New256Block38Checks.row31]
#print axioms solution
