-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block19
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:55:03.838602+00:00
-- url     : https://prove2.me/submissions/87b73e38-c0ad-45d8-9147-1918711f4035

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock19Checks
theorem row00 : RHFastWindow256CompactReference.checked (608+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (608+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (608+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (608+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (608+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (608+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (608+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (608+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (608+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (608+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (608+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (608+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (608+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (608+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (608+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (608+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (608+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (608+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (608+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (608+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (608+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (608+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (608+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (608+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (608+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (608+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (608+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (608+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (608+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (608+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (608+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (608+31)=true := by decide +kernel
end RHFastWindow256CompactBlock19Checks

theorem solution : RHFastWindow256CompactReference.block 608 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock19Checks.row00,
  RHFastWindow256CompactBlock19Checks.row01,
  RHFastWindow256CompactBlock19Checks.row02,
  RHFastWindow256CompactBlock19Checks.row03,
  RHFastWindow256CompactBlock19Checks.row04,
  RHFastWindow256CompactBlock19Checks.row05,
  RHFastWindow256CompactBlock19Checks.row06,
  RHFastWindow256CompactBlock19Checks.row07,
  RHFastWindow256CompactBlock19Checks.row08,
  RHFastWindow256CompactBlock19Checks.row09,
  RHFastWindow256CompactBlock19Checks.row10,
  RHFastWindow256CompactBlock19Checks.row11,
  RHFastWindow256CompactBlock19Checks.row12,
  RHFastWindow256CompactBlock19Checks.row13,
  RHFastWindow256CompactBlock19Checks.row14,
  RHFastWindow256CompactBlock19Checks.row15,
  RHFastWindow256CompactBlock19Checks.row16,
  RHFastWindow256CompactBlock19Checks.row17,
  RHFastWindow256CompactBlock19Checks.row18,
  RHFastWindow256CompactBlock19Checks.row19,
  RHFastWindow256CompactBlock19Checks.row20,
  RHFastWindow256CompactBlock19Checks.row21,
  RHFastWindow256CompactBlock19Checks.row22,
  RHFastWindow256CompactBlock19Checks.row23,
  RHFastWindow256CompactBlock19Checks.row24,
  RHFastWindow256CompactBlock19Checks.row25,
  RHFastWindow256CompactBlock19Checks.row26,
  RHFastWindow256CompactBlock19Checks.row27,
  RHFastWindow256CompactBlock19Checks.row28,
  RHFastWindow256CompactBlock19Checks.row29,
  RHFastWindow256CompactBlock19Checks.row30,
  RHFastWindow256CompactBlock19Checks.row31]
#print axioms solution
