-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block08
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:40:10.197284+00:00
-- url     : https://prove2.me/submissions/5c439be6-8c91-4954-88db-3256843b6a24

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock08Checks
theorem row00 : RHFastWindow256CompactReference.checked (256+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (256+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (256+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (256+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (256+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (256+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (256+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (256+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (256+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (256+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (256+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (256+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (256+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (256+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (256+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (256+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (256+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (256+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (256+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (256+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (256+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (256+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (256+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (256+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (256+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (256+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (256+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (256+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (256+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (256+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (256+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (256+31)=true := by decide +kernel
end RHFastWindow256CompactBlock08Checks

theorem solution : RHFastWindow256CompactReference.block 256 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock08Checks.row00,
  RHFastWindow256CompactBlock08Checks.row01,
  RHFastWindow256CompactBlock08Checks.row02,
  RHFastWindow256CompactBlock08Checks.row03,
  RHFastWindow256CompactBlock08Checks.row04,
  RHFastWindow256CompactBlock08Checks.row05,
  RHFastWindow256CompactBlock08Checks.row06,
  RHFastWindow256CompactBlock08Checks.row07,
  RHFastWindow256CompactBlock08Checks.row08,
  RHFastWindow256CompactBlock08Checks.row09,
  RHFastWindow256CompactBlock08Checks.row10,
  RHFastWindow256CompactBlock08Checks.row11,
  RHFastWindow256CompactBlock08Checks.row12,
  RHFastWindow256CompactBlock08Checks.row13,
  RHFastWindow256CompactBlock08Checks.row14,
  RHFastWindow256CompactBlock08Checks.row15,
  RHFastWindow256CompactBlock08Checks.row16,
  RHFastWindow256CompactBlock08Checks.row17,
  RHFastWindow256CompactBlock08Checks.row18,
  RHFastWindow256CompactBlock08Checks.row19,
  RHFastWindow256CompactBlock08Checks.row20,
  RHFastWindow256CompactBlock08Checks.row21,
  RHFastWindow256CompactBlock08Checks.row22,
  RHFastWindow256CompactBlock08Checks.row23,
  RHFastWindow256CompactBlock08Checks.row24,
  RHFastWindow256CompactBlock08Checks.row25,
  RHFastWindow256CompactBlock08Checks.row26,
  RHFastWindow256CompactBlock08Checks.row27,
  RHFastWindow256CompactBlock08Checks.row28,
  RHFastWindow256CompactBlock08Checks.row29,
  RHFastWindow256CompactBlock08Checks.row30,
  RHFastWindow256CompactBlock08Checks.row31]
#print axioms solution
