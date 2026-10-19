-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block18
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:53:39.856226+00:00
-- url     : https://prove2.me/submissions/073f80c1-c60f-4bd5-a1ba-3311125932c9

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock18Checks
theorem row00 : RHFastWindow256CompactReference.checked (576+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (576+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (576+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (576+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (576+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (576+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (576+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (576+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (576+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (576+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (576+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (576+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (576+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (576+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (576+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (576+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (576+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (576+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (576+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (576+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (576+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (576+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (576+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (576+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (576+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (576+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (576+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (576+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (576+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (576+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (576+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (576+31)=true := by decide +kernel
end RHFastWindow256CompactBlock18Checks

theorem solution : RHFastWindow256CompactReference.block 576 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock18Checks.row00,
  RHFastWindow256CompactBlock18Checks.row01,
  RHFastWindow256CompactBlock18Checks.row02,
  RHFastWindow256CompactBlock18Checks.row03,
  RHFastWindow256CompactBlock18Checks.row04,
  RHFastWindow256CompactBlock18Checks.row05,
  RHFastWindow256CompactBlock18Checks.row06,
  RHFastWindow256CompactBlock18Checks.row07,
  RHFastWindow256CompactBlock18Checks.row08,
  RHFastWindow256CompactBlock18Checks.row09,
  RHFastWindow256CompactBlock18Checks.row10,
  RHFastWindow256CompactBlock18Checks.row11,
  RHFastWindow256CompactBlock18Checks.row12,
  RHFastWindow256CompactBlock18Checks.row13,
  RHFastWindow256CompactBlock18Checks.row14,
  RHFastWindow256CompactBlock18Checks.row15,
  RHFastWindow256CompactBlock18Checks.row16,
  RHFastWindow256CompactBlock18Checks.row17,
  RHFastWindow256CompactBlock18Checks.row18,
  RHFastWindow256CompactBlock18Checks.row19,
  RHFastWindow256CompactBlock18Checks.row20,
  RHFastWindow256CompactBlock18Checks.row21,
  RHFastWindow256CompactBlock18Checks.row22,
  RHFastWindow256CompactBlock18Checks.row23,
  RHFastWindow256CompactBlock18Checks.row24,
  RHFastWindow256CompactBlock18Checks.row25,
  RHFastWindow256CompactBlock18Checks.row26,
  RHFastWindow256CompactBlock18Checks.row27,
  RHFastWindow256CompactBlock18Checks.row28,
  RHFastWindow256CompactBlock18Checks.row29,
  RHFastWindow256CompactBlock18Checks.row30,
  RHFastWindow256CompactBlock18Checks.row31]
#print axioms solution
