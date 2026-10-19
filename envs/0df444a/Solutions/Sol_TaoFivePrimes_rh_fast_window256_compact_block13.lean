-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block13
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:45:37.58412+00:00
-- url     : https://prove2.me/submissions/486504c7-43ba-44d1-a00f-444daa1a5468

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock13Checks
theorem row00 : RHFastWindow256CompactReference.checked (416+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (416+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (416+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (416+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (416+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (416+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (416+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (416+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (416+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (416+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (416+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (416+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (416+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (416+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (416+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (416+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (416+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (416+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (416+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (416+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (416+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (416+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (416+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (416+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (416+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (416+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (416+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (416+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (416+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (416+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (416+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (416+31)=true := by decide +kernel
end RHFastWindow256CompactBlock13Checks

theorem solution : RHFastWindow256CompactReference.block 416 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock13Checks.row00,
  RHFastWindow256CompactBlock13Checks.row01,
  RHFastWindow256CompactBlock13Checks.row02,
  RHFastWindow256CompactBlock13Checks.row03,
  RHFastWindow256CompactBlock13Checks.row04,
  RHFastWindow256CompactBlock13Checks.row05,
  RHFastWindow256CompactBlock13Checks.row06,
  RHFastWindow256CompactBlock13Checks.row07,
  RHFastWindow256CompactBlock13Checks.row08,
  RHFastWindow256CompactBlock13Checks.row09,
  RHFastWindow256CompactBlock13Checks.row10,
  RHFastWindow256CompactBlock13Checks.row11,
  RHFastWindow256CompactBlock13Checks.row12,
  RHFastWindow256CompactBlock13Checks.row13,
  RHFastWindow256CompactBlock13Checks.row14,
  RHFastWindow256CompactBlock13Checks.row15,
  RHFastWindow256CompactBlock13Checks.row16,
  RHFastWindow256CompactBlock13Checks.row17,
  RHFastWindow256CompactBlock13Checks.row18,
  RHFastWindow256CompactBlock13Checks.row19,
  RHFastWindow256CompactBlock13Checks.row20,
  RHFastWindow256CompactBlock13Checks.row21,
  RHFastWindow256CompactBlock13Checks.row22,
  RHFastWindow256CompactBlock13Checks.row23,
  RHFastWindow256CompactBlock13Checks.row24,
  RHFastWindow256CompactBlock13Checks.row25,
  RHFastWindow256CompactBlock13Checks.row26,
  RHFastWindow256CompactBlock13Checks.row27,
  RHFastWindow256CompactBlock13Checks.row28,
  RHFastWindow256CompactBlock13Checks.row29,
  RHFastWindow256CompactBlock13Checks.row30,
  RHFastWindow256CompactBlock13Checks.row31]
#print axioms solution
