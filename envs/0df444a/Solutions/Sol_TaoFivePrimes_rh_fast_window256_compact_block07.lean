-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:41:15.500371+00:00
-- url     : https://prove2.me/submissions/a8587822-431c-4732-aade-65f00f3ccb4b

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock07Checks
theorem row00 : RHFastWindow256CompactReference.checked (224+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (224+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (224+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (224+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (224+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (224+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (224+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (224+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (224+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (224+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (224+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (224+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (224+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (224+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (224+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (224+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (224+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (224+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (224+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (224+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (224+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (224+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (224+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (224+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (224+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (224+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (224+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (224+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (224+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (224+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (224+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (224+31)=true := by decide +kernel
end RHFastWindow256CompactBlock07Checks

theorem solution : RHFastWindow256CompactReference.block 224 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock07Checks.row00,
  RHFastWindow256CompactBlock07Checks.row01,
  RHFastWindow256CompactBlock07Checks.row02,
  RHFastWindow256CompactBlock07Checks.row03,
  RHFastWindow256CompactBlock07Checks.row04,
  RHFastWindow256CompactBlock07Checks.row05,
  RHFastWindow256CompactBlock07Checks.row06,
  RHFastWindow256CompactBlock07Checks.row07,
  RHFastWindow256CompactBlock07Checks.row08,
  RHFastWindow256CompactBlock07Checks.row09,
  RHFastWindow256CompactBlock07Checks.row10,
  RHFastWindow256CompactBlock07Checks.row11,
  RHFastWindow256CompactBlock07Checks.row12,
  RHFastWindow256CompactBlock07Checks.row13,
  RHFastWindow256CompactBlock07Checks.row14,
  RHFastWindow256CompactBlock07Checks.row15,
  RHFastWindow256CompactBlock07Checks.row16,
  RHFastWindow256CompactBlock07Checks.row17,
  RHFastWindow256CompactBlock07Checks.row18,
  RHFastWindow256CompactBlock07Checks.row19,
  RHFastWindow256CompactBlock07Checks.row20,
  RHFastWindow256CompactBlock07Checks.row21,
  RHFastWindow256CompactBlock07Checks.row22,
  RHFastWindow256CompactBlock07Checks.row23,
  RHFastWindow256CompactBlock07Checks.row24,
  RHFastWindow256CompactBlock07Checks.row25,
  RHFastWindow256CompactBlock07Checks.row26,
  RHFastWindow256CompactBlock07Checks.row27,
  RHFastWindow256CompactBlock07Checks.row28,
  RHFastWindow256CompactBlock07Checks.row29,
  RHFastWindow256CompactBlock07Checks.row30,
  RHFastWindow256CompactBlock07Checks.row31]
#print axioms solution
