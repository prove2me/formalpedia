-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block53
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:25:57.592108+00:00
-- url     : https://prove2.me/submissions/e89144d9-98c7-4711-90ad-6c3bfdea92e7

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock53Checks
theorem row00 : RHFastWindow256CompactReference.checked (1696+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1696+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1696+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1696+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1696+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1696+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1696+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1696+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1696+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1696+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1696+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1696+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1696+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1696+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1696+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1696+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1696+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1696+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1696+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1696+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1696+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1696+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1696+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1696+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1696+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1696+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1696+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1696+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1696+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1696+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1696+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1696+31)=true := by decide +kernel
end RHFastWindow256CompactBlock53Checks

theorem solution : RHFastWindow256CompactReference.block 1696 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock53Checks.row00,
  RHFastWindow256CompactBlock53Checks.row01,
  RHFastWindow256CompactBlock53Checks.row02,
  RHFastWindow256CompactBlock53Checks.row03,
  RHFastWindow256CompactBlock53Checks.row04,
  RHFastWindow256CompactBlock53Checks.row05,
  RHFastWindow256CompactBlock53Checks.row06,
  RHFastWindow256CompactBlock53Checks.row07,
  RHFastWindow256CompactBlock53Checks.row08,
  RHFastWindow256CompactBlock53Checks.row09,
  RHFastWindow256CompactBlock53Checks.row10,
  RHFastWindow256CompactBlock53Checks.row11,
  RHFastWindow256CompactBlock53Checks.row12,
  RHFastWindow256CompactBlock53Checks.row13,
  RHFastWindow256CompactBlock53Checks.row14,
  RHFastWindow256CompactBlock53Checks.row15,
  RHFastWindow256CompactBlock53Checks.row16,
  RHFastWindow256CompactBlock53Checks.row17,
  RHFastWindow256CompactBlock53Checks.row18,
  RHFastWindow256CompactBlock53Checks.row19,
  RHFastWindow256CompactBlock53Checks.row20,
  RHFastWindow256CompactBlock53Checks.row21,
  RHFastWindow256CompactBlock53Checks.row22,
  RHFastWindow256CompactBlock53Checks.row23,
  RHFastWindow256CompactBlock53Checks.row24,
  RHFastWindow256CompactBlock53Checks.row25,
  RHFastWindow256CompactBlock53Checks.row26,
  RHFastWindow256CompactBlock53Checks.row27,
  RHFastWindow256CompactBlock53Checks.row28,
  RHFastWindow256CompactBlock53Checks.row29,
  RHFastWindow256CompactBlock53Checks.row30,
  RHFastWindow256CompactBlock53Checks.row31]
#print axioms solution
