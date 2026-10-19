-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block54
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:26:23.999841+00:00
-- url     : https://prove2.me/submissions/e5d3ee19-e2e4-446e-90e5-771d6c0500e4

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock54Checks
theorem row00 : RHFastWindow256CompactReference.checked (1728+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1728+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1728+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1728+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1728+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1728+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1728+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1728+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1728+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1728+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1728+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1728+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1728+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1728+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1728+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1728+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1728+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1728+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1728+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1728+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1728+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1728+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1728+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1728+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1728+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1728+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1728+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1728+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1728+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1728+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1728+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1728+31)=true := by decide +kernel
end RHFastWindow256CompactBlock54Checks

theorem solution : RHFastWindow256CompactReference.block 1728 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock54Checks.row00,
  RHFastWindow256CompactBlock54Checks.row01,
  RHFastWindow256CompactBlock54Checks.row02,
  RHFastWindow256CompactBlock54Checks.row03,
  RHFastWindow256CompactBlock54Checks.row04,
  RHFastWindow256CompactBlock54Checks.row05,
  RHFastWindow256CompactBlock54Checks.row06,
  RHFastWindow256CompactBlock54Checks.row07,
  RHFastWindow256CompactBlock54Checks.row08,
  RHFastWindow256CompactBlock54Checks.row09,
  RHFastWindow256CompactBlock54Checks.row10,
  RHFastWindow256CompactBlock54Checks.row11,
  RHFastWindow256CompactBlock54Checks.row12,
  RHFastWindow256CompactBlock54Checks.row13,
  RHFastWindow256CompactBlock54Checks.row14,
  RHFastWindow256CompactBlock54Checks.row15,
  RHFastWindow256CompactBlock54Checks.row16,
  RHFastWindow256CompactBlock54Checks.row17,
  RHFastWindow256CompactBlock54Checks.row18,
  RHFastWindow256CompactBlock54Checks.row19,
  RHFastWindow256CompactBlock54Checks.row20,
  RHFastWindow256CompactBlock54Checks.row21,
  RHFastWindow256CompactBlock54Checks.row22,
  RHFastWindow256CompactBlock54Checks.row23,
  RHFastWindow256CompactBlock54Checks.row24,
  RHFastWindow256CompactBlock54Checks.row25,
  RHFastWindow256CompactBlock54Checks.row26,
  RHFastWindow256CompactBlock54Checks.row27,
  RHFastWindow256CompactBlock54Checks.row28,
  RHFastWindow256CompactBlock54Checks.row29,
  RHFastWindow256CompactBlock54Checks.row30,
  RHFastWindow256CompactBlock54Checks.row31]
#print axioms solution
