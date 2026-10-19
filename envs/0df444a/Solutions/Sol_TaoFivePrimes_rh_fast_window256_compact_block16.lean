-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block16
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:48:41.132193+00:00
-- url     : https://prove2.me/submissions/af81c11f-056c-41e0-adba-ec7a8e9c7d6f

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock16Checks
theorem row00 : RHFastWindow256CompactReference.checked (512+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (512+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (512+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (512+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (512+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (512+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (512+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (512+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (512+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (512+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (512+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (512+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (512+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (512+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (512+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (512+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (512+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (512+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (512+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (512+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (512+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (512+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (512+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (512+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (512+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (512+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (512+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (512+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (512+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (512+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (512+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (512+31)=true := by decide +kernel
end RHFastWindow256CompactBlock16Checks

theorem solution : RHFastWindow256CompactReference.block 512 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock16Checks.row00,
  RHFastWindow256CompactBlock16Checks.row01,
  RHFastWindow256CompactBlock16Checks.row02,
  RHFastWindow256CompactBlock16Checks.row03,
  RHFastWindow256CompactBlock16Checks.row04,
  RHFastWindow256CompactBlock16Checks.row05,
  RHFastWindow256CompactBlock16Checks.row06,
  RHFastWindow256CompactBlock16Checks.row07,
  RHFastWindow256CompactBlock16Checks.row08,
  RHFastWindow256CompactBlock16Checks.row09,
  RHFastWindow256CompactBlock16Checks.row10,
  RHFastWindow256CompactBlock16Checks.row11,
  RHFastWindow256CompactBlock16Checks.row12,
  RHFastWindow256CompactBlock16Checks.row13,
  RHFastWindow256CompactBlock16Checks.row14,
  RHFastWindow256CompactBlock16Checks.row15,
  RHFastWindow256CompactBlock16Checks.row16,
  RHFastWindow256CompactBlock16Checks.row17,
  RHFastWindow256CompactBlock16Checks.row18,
  RHFastWindow256CompactBlock16Checks.row19,
  RHFastWindow256CompactBlock16Checks.row20,
  RHFastWindow256CompactBlock16Checks.row21,
  RHFastWindow256CompactBlock16Checks.row22,
  RHFastWindow256CompactBlock16Checks.row23,
  RHFastWindow256CompactBlock16Checks.row24,
  RHFastWindow256CompactBlock16Checks.row25,
  RHFastWindow256CompactBlock16Checks.row26,
  RHFastWindow256CompactBlock16Checks.row27,
  RHFastWindow256CompactBlock16Checks.row28,
  RHFastWindow256CompactBlock16Checks.row29,
  RHFastWindow256CompactBlock16Checks.row30,
  RHFastWindow256CompactBlock16Checks.row31]
#print axioms solution
