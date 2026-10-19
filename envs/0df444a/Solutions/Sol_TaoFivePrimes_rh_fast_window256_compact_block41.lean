-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block41
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:14:14.740145+00:00
-- url     : https://prove2.me/submissions/103bf7a5-c5e8-412a-b301-cf523543ea48

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock41Checks
theorem row00 : RHFastWindow256CompactReference.checked (1312+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1312+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1312+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1312+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1312+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1312+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1312+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1312+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1312+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1312+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1312+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1312+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1312+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1312+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1312+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1312+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1312+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1312+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1312+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1312+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1312+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1312+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1312+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1312+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1312+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1312+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1312+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1312+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1312+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1312+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1312+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1312+31)=true := by decide +kernel
end RHFastWindow256CompactBlock41Checks

theorem solution : RHFastWindow256CompactReference.block 1312 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock41Checks.row00,
  RHFastWindow256CompactBlock41Checks.row01,
  RHFastWindow256CompactBlock41Checks.row02,
  RHFastWindow256CompactBlock41Checks.row03,
  RHFastWindow256CompactBlock41Checks.row04,
  RHFastWindow256CompactBlock41Checks.row05,
  RHFastWindow256CompactBlock41Checks.row06,
  RHFastWindow256CompactBlock41Checks.row07,
  RHFastWindow256CompactBlock41Checks.row08,
  RHFastWindow256CompactBlock41Checks.row09,
  RHFastWindow256CompactBlock41Checks.row10,
  RHFastWindow256CompactBlock41Checks.row11,
  RHFastWindow256CompactBlock41Checks.row12,
  RHFastWindow256CompactBlock41Checks.row13,
  RHFastWindow256CompactBlock41Checks.row14,
  RHFastWindow256CompactBlock41Checks.row15,
  RHFastWindow256CompactBlock41Checks.row16,
  RHFastWindow256CompactBlock41Checks.row17,
  RHFastWindow256CompactBlock41Checks.row18,
  RHFastWindow256CompactBlock41Checks.row19,
  RHFastWindow256CompactBlock41Checks.row20,
  RHFastWindow256CompactBlock41Checks.row21,
  RHFastWindow256CompactBlock41Checks.row22,
  RHFastWindow256CompactBlock41Checks.row23,
  RHFastWindow256CompactBlock41Checks.row24,
  RHFastWindow256CompactBlock41Checks.row25,
  RHFastWindow256CompactBlock41Checks.row26,
  RHFastWindow256CompactBlock41Checks.row27,
  RHFastWindow256CompactBlock41Checks.row28,
  RHFastWindow256CompactBlock41Checks.row29,
  RHFastWindow256CompactBlock41Checks.row30,
  RHFastWindow256CompactBlock41Checks.row31]
#print axioms solution
