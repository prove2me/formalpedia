-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block40
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:13:14.055026+00:00
-- url     : https://prove2.me/submissions/c09524b5-432c-4b5f-b774-65f0f4557bd3

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock40Checks
theorem row00 : RHFastWindow256CompactReference.checked (1280+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1280+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1280+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1280+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1280+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1280+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1280+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1280+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1280+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1280+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1280+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1280+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1280+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1280+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1280+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1280+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1280+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1280+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1280+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1280+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1280+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1280+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1280+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1280+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1280+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1280+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1280+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1280+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1280+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1280+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1280+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1280+31)=true := by decide +kernel
end RHFastWindow256CompactBlock40Checks

theorem solution : RHFastWindow256CompactReference.block 1280 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock40Checks.row00,
  RHFastWindow256CompactBlock40Checks.row01,
  RHFastWindow256CompactBlock40Checks.row02,
  RHFastWindow256CompactBlock40Checks.row03,
  RHFastWindow256CompactBlock40Checks.row04,
  RHFastWindow256CompactBlock40Checks.row05,
  RHFastWindow256CompactBlock40Checks.row06,
  RHFastWindow256CompactBlock40Checks.row07,
  RHFastWindow256CompactBlock40Checks.row08,
  RHFastWindow256CompactBlock40Checks.row09,
  RHFastWindow256CompactBlock40Checks.row10,
  RHFastWindow256CompactBlock40Checks.row11,
  RHFastWindow256CompactBlock40Checks.row12,
  RHFastWindow256CompactBlock40Checks.row13,
  RHFastWindow256CompactBlock40Checks.row14,
  RHFastWindow256CompactBlock40Checks.row15,
  RHFastWindow256CompactBlock40Checks.row16,
  RHFastWindow256CompactBlock40Checks.row17,
  RHFastWindow256CompactBlock40Checks.row18,
  RHFastWindow256CompactBlock40Checks.row19,
  RHFastWindow256CompactBlock40Checks.row20,
  RHFastWindow256CompactBlock40Checks.row21,
  RHFastWindow256CompactBlock40Checks.row22,
  RHFastWindow256CompactBlock40Checks.row23,
  RHFastWindow256CompactBlock40Checks.row24,
  RHFastWindow256CompactBlock40Checks.row25,
  RHFastWindow256CompactBlock40Checks.row26,
  RHFastWindow256CompactBlock40Checks.row27,
  RHFastWindow256CompactBlock40Checks.row28,
  RHFastWindow256CompactBlock40Checks.row29,
  RHFastWindow256CompactBlock40Checks.row30,
  RHFastWindow256CompactBlock40Checks.row31]
#print axioms solution
