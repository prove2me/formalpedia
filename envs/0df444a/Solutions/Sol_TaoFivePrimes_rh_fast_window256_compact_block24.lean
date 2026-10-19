-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block24
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:57:50.019935+00:00
-- url     : https://prove2.me/submissions/c9348c6a-861e-4b1c-859f-f92812b0a765

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock24Checks
theorem row00 : RHFastWindow256CompactReference.checked (768+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (768+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (768+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (768+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (768+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (768+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (768+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (768+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (768+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (768+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (768+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (768+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (768+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (768+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (768+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (768+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (768+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (768+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (768+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (768+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (768+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (768+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (768+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (768+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (768+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (768+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (768+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (768+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (768+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (768+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (768+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (768+31)=true := by decide +kernel
end RHFastWindow256CompactBlock24Checks

theorem solution : RHFastWindow256CompactReference.block 768 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock24Checks.row00,
  RHFastWindow256CompactBlock24Checks.row01,
  RHFastWindow256CompactBlock24Checks.row02,
  RHFastWindow256CompactBlock24Checks.row03,
  RHFastWindow256CompactBlock24Checks.row04,
  RHFastWindow256CompactBlock24Checks.row05,
  RHFastWindow256CompactBlock24Checks.row06,
  RHFastWindow256CompactBlock24Checks.row07,
  RHFastWindow256CompactBlock24Checks.row08,
  RHFastWindow256CompactBlock24Checks.row09,
  RHFastWindow256CompactBlock24Checks.row10,
  RHFastWindow256CompactBlock24Checks.row11,
  RHFastWindow256CompactBlock24Checks.row12,
  RHFastWindow256CompactBlock24Checks.row13,
  RHFastWindow256CompactBlock24Checks.row14,
  RHFastWindow256CompactBlock24Checks.row15,
  RHFastWindow256CompactBlock24Checks.row16,
  RHFastWindow256CompactBlock24Checks.row17,
  RHFastWindow256CompactBlock24Checks.row18,
  RHFastWindow256CompactBlock24Checks.row19,
  RHFastWindow256CompactBlock24Checks.row20,
  RHFastWindow256CompactBlock24Checks.row21,
  RHFastWindow256CompactBlock24Checks.row22,
  RHFastWindow256CompactBlock24Checks.row23,
  RHFastWindow256CompactBlock24Checks.row24,
  RHFastWindow256CompactBlock24Checks.row25,
  RHFastWindow256CompactBlock24Checks.row26,
  RHFastWindow256CompactBlock24Checks.row27,
  RHFastWindow256CompactBlock24Checks.row28,
  RHFastWindow256CompactBlock24Checks.row29,
  RHFastWindow256CompactBlock24Checks.row30,
  RHFastWindow256CompactBlock24Checks.row31]
#print axioms solution
