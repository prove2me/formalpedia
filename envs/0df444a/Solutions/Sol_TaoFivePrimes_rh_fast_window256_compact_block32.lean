-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block32
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:05:59.183766+00:00
-- url     : https://prove2.me/submissions/36baca48-5eb0-4568-b059-6b8e1abece6f

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock32Checks
theorem row00 : RHFastWindow256CompactReference.checked (1024+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1024+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1024+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1024+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1024+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1024+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1024+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1024+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1024+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1024+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1024+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1024+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1024+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1024+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1024+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1024+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1024+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1024+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1024+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1024+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1024+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1024+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1024+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1024+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1024+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1024+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1024+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1024+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1024+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1024+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1024+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1024+31)=true := by decide +kernel
end RHFastWindow256CompactBlock32Checks

theorem solution : RHFastWindow256CompactReference.block 1024 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock32Checks.row00,
  RHFastWindow256CompactBlock32Checks.row01,
  RHFastWindow256CompactBlock32Checks.row02,
  RHFastWindow256CompactBlock32Checks.row03,
  RHFastWindow256CompactBlock32Checks.row04,
  RHFastWindow256CompactBlock32Checks.row05,
  RHFastWindow256CompactBlock32Checks.row06,
  RHFastWindow256CompactBlock32Checks.row07,
  RHFastWindow256CompactBlock32Checks.row08,
  RHFastWindow256CompactBlock32Checks.row09,
  RHFastWindow256CompactBlock32Checks.row10,
  RHFastWindow256CompactBlock32Checks.row11,
  RHFastWindow256CompactBlock32Checks.row12,
  RHFastWindow256CompactBlock32Checks.row13,
  RHFastWindow256CompactBlock32Checks.row14,
  RHFastWindow256CompactBlock32Checks.row15,
  RHFastWindow256CompactBlock32Checks.row16,
  RHFastWindow256CompactBlock32Checks.row17,
  RHFastWindow256CompactBlock32Checks.row18,
  RHFastWindow256CompactBlock32Checks.row19,
  RHFastWindow256CompactBlock32Checks.row20,
  RHFastWindow256CompactBlock32Checks.row21,
  RHFastWindow256CompactBlock32Checks.row22,
  RHFastWindow256CompactBlock32Checks.row23,
  RHFastWindow256CompactBlock32Checks.row24,
  RHFastWindow256CompactBlock32Checks.row25,
  RHFastWindow256CompactBlock32Checks.row26,
  RHFastWindow256CompactBlock32Checks.row27,
  RHFastWindow256CompactBlock32Checks.row28,
  RHFastWindow256CompactBlock32Checks.row29,
  RHFastWindow256CompactBlock32Checks.row30,
  RHFastWindow256CompactBlock32Checks.row31]
#print axioms solution
