-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block42
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:15:44.348426+00:00
-- url     : https://prove2.me/submissions/53f39642-54a3-4489-9e15-86bdcbd0319e

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock42Checks
theorem row00 : RHFastWindow256CompactReference.checked (1344+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1344+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1344+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1344+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1344+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1344+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1344+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1344+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1344+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1344+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1344+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1344+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1344+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1344+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1344+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1344+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1344+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1344+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1344+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1344+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1344+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1344+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1344+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1344+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1344+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1344+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1344+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1344+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1344+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1344+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1344+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1344+31)=true := by decide +kernel
end RHFastWindow256CompactBlock42Checks

theorem solution : RHFastWindow256CompactReference.block 1344 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock42Checks.row00,
  RHFastWindow256CompactBlock42Checks.row01,
  RHFastWindow256CompactBlock42Checks.row02,
  RHFastWindow256CompactBlock42Checks.row03,
  RHFastWindow256CompactBlock42Checks.row04,
  RHFastWindow256CompactBlock42Checks.row05,
  RHFastWindow256CompactBlock42Checks.row06,
  RHFastWindow256CompactBlock42Checks.row07,
  RHFastWindow256CompactBlock42Checks.row08,
  RHFastWindow256CompactBlock42Checks.row09,
  RHFastWindow256CompactBlock42Checks.row10,
  RHFastWindow256CompactBlock42Checks.row11,
  RHFastWindow256CompactBlock42Checks.row12,
  RHFastWindow256CompactBlock42Checks.row13,
  RHFastWindow256CompactBlock42Checks.row14,
  RHFastWindow256CompactBlock42Checks.row15,
  RHFastWindow256CompactBlock42Checks.row16,
  RHFastWindow256CompactBlock42Checks.row17,
  RHFastWindow256CompactBlock42Checks.row18,
  RHFastWindow256CompactBlock42Checks.row19,
  RHFastWindow256CompactBlock42Checks.row20,
  RHFastWindow256CompactBlock42Checks.row21,
  RHFastWindow256CompactBlock42Checks.row22,
  RHFastWindow256CompactBlock42Checks.row23,
  RHFastWindow256CompactBlock42Checks.row24,
  RHFastWindow256CompactBlock42Checks.row25,
  RHFastWindow256CompactBlock42Checks.row26,
  RHFastWindow256CompactBlock42Checks.row27,
  RHFastWindow256CompactBlock42Checks.row28,
  RHFastWindow256CompactBlock42Checks.row29,
  RHFastWindow256CompactBlock42Checks.row30,
  RHFastWindow256CompactBlock42Checks.row31]
#print axioms solution
