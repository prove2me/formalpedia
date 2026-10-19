-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block52
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:25:30.90096+00:00
-- url     : https://prove2.me/submissions/e3f3a573-108d-4dbf-9230-d9f78e58b248

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock52Checks
theorem row00 : RHFastWindow256CompactReference.checked (1664+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1664+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1664+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1664+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1664+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1664+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1664+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1664+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1664+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1664+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1664+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1664+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1664+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1664+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1664+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1664+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1664+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1664+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1664+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1664+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1664+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1664+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1664+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1664+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1664+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1664+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1664+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1664+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1664+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1664+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1664+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1664+31)=true := by decide +kernel
end RHFastWindow256CompactBlock52Checks

theorem solution : RHFastWindow256CompactReference.block 1664 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock52Checks.row00,
  RHFastWindow256CompactBlock52Checks.row01,
  RHFastWindow256CompactBlock52Checks.row02,
  RHFastWindow256CompactBlock52Checks.row03,
  RHFastWindow256CompactBlock52Checks.row04,
  RHFastWindow256CompactBlock52Checks.row05,
  RHFastWindow256CompactBlock52Checks.row06,
  RHFastWindow256CompactBlock52Checks.row07,
  RHFastWindow256CompactBlock52Checks.row08,
  RHFastWindow256CompactBlock52Checks.row09,
  RHFastWindow256CompactBlock52Checks.row10,
  RHFastWindow256CompactBlock52Checks.row11,
  RHFastWindow256CompactBlock52Checks.row12,
  RHFastWindow256CompactBlock52Checks.row13,
  RHFastWindow256CompactBlock52Checks.row14,
  RHFastWindow256CompactBlock52Checks.row15,
  RHFastWindow256CompactBlock52Checks.row16,
  RHFastWindow256CompactBlock52Checks.row17,
  RHFastWindow256CompactBlock52Checks.row18,
  RHFastWindow256CompactBlock52Checks.row19,
  RHFastWindow256CompactBlock52Checks.row20,
  RHFastWindow256CompactBlock52Checks.row21,
  RHFastWindow256CompactBlock52Checks.row22,
  RHFastWindow256CompactBlock52Checks.row23,
  RHFastWindow256CompactBlock52Checks.row24,
  RHFastWindow256CompactBlock52Checks.row25,
  RHFastWindow256CompactBlock52Checks.row26,
  RHFastWindow256CompactBlock52Checks.row27,
  RHFastWindow256CompactBlock52Checks.row28,
  RHFastWindow256CompactBlock52Checks.row29,
  RHFastWindow256CompactBlock52Checks.row30,
  RHFastWindow256CompactBlock52Checks.row31]
#print axioms solution
