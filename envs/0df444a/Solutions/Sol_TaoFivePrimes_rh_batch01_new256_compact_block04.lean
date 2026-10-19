-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_compact_block04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:33:09.543541+00:00
-- url     : https://prove2.me/submissions/955fb623-1e1c-40d1-b91f-8546c66bc7d0

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHBatch01New256Block04Checks
theorem row00 : RHBatch01New256CompactReference.checked (128+0)=true := by decide +kernel
theorem row01 : RHBatch01New256CompactReference.checked (128+1)=true := by decide +kernel
theorem row02 : RHBatch01New256CompactReference.checked (128+2)=true := by decide +kernel
theorem row03 : RHBatch01New256CompactReference.checked (128+3)=true := by decide +kernel
theorem row04 : RHBatch01New256CompactReference.checked (128+4)=true := by decide +kernel
theorem row05 : RHBatch01New256CompactReference.checked (128+5)=true := by decide +kernel
theorem row06 : RHBatch01New256CompactReference.checked (128+6)=true := by decide +kernel
theorem row07 : RHBatch01New256CompactReference.checked (128+7)=true := by decide +kernel
theorem row08 : RHBatch01New256CompactReference.checked (128+8)=true := by decide +kernel
theorem row09 : RHBatch01New256CompactReference.checked (128+9)=true := by decide +kernel
theorem row10 : RHBatch01New256CompactReference.checked (128+10)=true := by decide +kernel
theorem row11 : RHBatch01New256CompactReference.checked (128+11)=true := by decide +kernel
theorem row12 : RHBatch01New256CompactReference.checked (128+12)=true := by decide +kernel
theorem row13 : RHBatch01New256CompactReference.checked (128+13)=true := by decide +kernel
theorem row14 : RHBatch01New256CompactReference.checked (128+14)=true := by decide +kernel
theorem row15 : RHBatch01New256CompactReference.checked (128+15)=true := by decide +kernel
theorem row16 : RHBatch01New256CompactReference.checked (128+16)=true := by decide +kernel
theorem row17 : RHBatch01New256CompactReference.checked (128+17)=true := by decide +kernel
theorem row18 : RHBatch01New256CompactReference.checked (128+18)=true := by decide +kernel
theorem row19 : RHBatch01New256CompactReference.checked (128+19)=true := by decide +kernel
theorem row20 : RHBatch01New256CompactReference.checked (128+20)=true := by decide +kernel
theorem row21 : RHBatch01New256CompactReference.checked (128+21)=true := by decide +kernel
theorem row22 : RHBatch01New256CompactReference.checked (128+22)=true := by decide +kernel
theorem row23 : RHBatch01New256CompactReference.checked (128+23)=true := by decide +kernel
theorem row24 : RHBatch01New256CompactReference.checked (128+24)=true := by decide +kernel
theorem row25 : RHBatch01New256CompactReference.checked (128+25)=true := by decide +kernel
theorem row26 : RHBatch01New256CompactReference.checked (128+26)=true := by decide +kernel
theorem row27 : RHBatch01New256CompactReference.checked (128+27)=true := by decide +kernel
theorem row28 : RHBatch01New256CompactReference.checked (128+28)=true := by decide +kernel
theorem row29 : RHBatch01New256CompactReference.checked (128+29)=true := by decide +kernel
theorem row30 : RHBatch01New256CompactReference.checked (128+30)=true := by decide +kernel
theorem row31 : RHBatch01New256CompactReference.checked (128+31)=true := by decide +kernel
end RHBatch01New256Block04Checks

theorem solution : RHBatch01New256CompactReference.block 128 32=true := by
 simp only [RHBatch01New256CompactReference.block,List.range_succ,List.range_zero,List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHBatch01New256Block04Checks.row00,RHBatch01New256Block04Checks.row01,RHBatch01New256Block04Checks.row02,RHBatch01New256Block04Checks.row03,RHBatch01New256Block04Checks.row04,RHBatch01New256Block04Checks.row05,RHBatch01New256Block04Checks.row06,RHBatch01New256Block04Checks.row07,RHBatch01New256Block04Checks.row08,RHBatch01New256Block04Checks.row09,RHBatch01New256Block04Checks.row10,RHBatch01New256Block04Checks.row11,RHBatch01New256Block04Checks.row12,RHBatch01New256Block04Checks.row13,RHBatch01New256Block04Checks.row14,RHBatch01New256Block04Checks.row15,RHBatch01New256Block04Checks.row16,RHBatch01New256Block04Checks.row17,RHBatch01New256Block04Checks.row18,RHBatch01New256Block04Checks.row19,RHBatch01New256Block04Checks.row20,RHBatch01New256Block04Checks.row21,RHBatch01New256Block04Checks.row22,RHBatch01New256Block04Checks.row23,RHBatch01New256Block04Checks.row24,RHBatch01New256Block04Checks.row25,RHBatch01New256Block04Checks.row26,RHBatch01New256Block04Checks.row27,RHBatch01New256Block04Checks.row28,RHBatch01New256Block04Checks.row29,RHBatch01New256Block04Checks.row30,RHBatch01New256Block04Checks.row31]
#print axioms solution
