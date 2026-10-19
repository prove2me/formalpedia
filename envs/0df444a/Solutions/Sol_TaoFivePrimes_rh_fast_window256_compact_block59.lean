-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block59
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:31:42.98565+00:00
-- url     : https://prove2.me/submissions/7b21ef43-67c8-4fa0-b74c-ed81ce9e42e2

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock59Checks
theorem row00 : RHFastWindow256CompactReference.checked (1888+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1888+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1888+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1888+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1888+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1888+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1888+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1888+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1888+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1888+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1888+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1888+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1888+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1888+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1888+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1888+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1888+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1888+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1888+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1888+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1888+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1888+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1888+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1888+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1888+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1888+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1888+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1888+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1888+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1888+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1888+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1888+31)=true := by decide +kernel
end RHFastWindow256CompactBlock59Checks

theorem solution : RHFastWindow256CompactReference.block 1888 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock59Checks.row00,
  RHFastWindow256CompactBlock59Checks.row01,
  RHFastWindow256CompactBlock59Checks.row02,
  RHFastWindow256CompactBlock59Checks.row03,
  RHFastWindow256CompactBlock59Checks.row04,
  RHFastWindow256CompactBlock59Checks.row05,
  RHFastWindow256CompactBlock59Checks.row06,
  RHFastWindow256CompactBlock59Checks.row07,
  RHFastWindow256CompactBlock59Checks.row08,
  RHFastWindow256CompactBlock59Checks.row09,
  RHFastWindow256CompactBlock59Checks.row10,
  RHFastWindow256CompactBlock59Checks.row11,
  RHFastWindow256CompactBlock59Checks.row12,
  RHFastWindow256CompactBlock59Checks.row13,
  RHFastWindow256CompactBlock59Checks.row14,
  RHFastWindow256CompactBlock59Checks.row15,
  RHFastWindow256CompactBlock59Checks.row16,
  RHFastWindow256CompactBlock59Checks.row17,
  RHFastWindow256CompactBlock59Checks.row18,
  RHFastWindow256CompactBlock59Checks.row19,
  RHFastWindow256CompactBlock59Checks.row20,
  RHFastWindow256CompactBlock59Checks.row21,
  RHFastWindow256CompactBlock59Checks.row22,
  RHFastWindow256CompactBlock59Checks.row23,
  RHFastWindow256CompactBlock59Checks.row24,
  RHFastWindow256CompactBlock59Checks.row25,
  RHFastWindow256CompactBlock59Checks.row26,
  RHFastWindow256CompactBlock59Checks.row27,
  RHFastWindow256CompactBlock59Checks.row28,
  RHFastWindow256CompactBlock59Checks.row29,
  RHFastWindow256CompactBlock59Checks.row30,
  RHFastWindow256CompactBlock59Checks.row31]
#print axioms solution
