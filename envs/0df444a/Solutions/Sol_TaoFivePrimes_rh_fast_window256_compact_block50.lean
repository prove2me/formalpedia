-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block50
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:22:50.379543+00:00
-- url     : https://prove2.me/submissions/cc1b65a6-1879-4952-bf0a-f8319f7764cc

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock50Checks
theorem row00 : RHFastWindow256CompactReference.checked (1600+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1600+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1600+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1600+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1600+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1600+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1600+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1600+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1600+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1600+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1600+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1600+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1600+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1600+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1600+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1600+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1600+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1600+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1600+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1600+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1600+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1600+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1600+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1600+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1600+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1600+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1600+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1600+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1600+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1600+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1600+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1600+31)=true := by decide +kernel
end RHFastWindow256CompactBlock50Checks

theorem solution : RHFastWindow256CompactReference.block 1600 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock50Checks.row00,
  RHFastWindow256CompactBlock50Checks.row01,
  RHFastWindow256CompactBlock50Checks.row02,
  RHFastWindow256CompactBlock50Checks.row03,
  RHFastWindow256CompactBlock50Checks.row04,
  RHFastWindow256CompactBlock50Checks.row05,
  RHFastWindow256CompactBlock50Checks.row06,
  RHFastWindow256CompactBlock50Checks.row07,
  RHFastWindow256CompactBlock50Checks.row08,
  RHFastWindow256CompactBlock50Checks.row09,
  RHFastWindow256CompactBlock50Checks.row10,
  RHFastWindow256CompactBlock50Checks.row11,
  RHFastWindow256CompactBlock50Checks.row12,
  RHFastWindow256CompactBlock50Checks.row13,
  RHFastWindow256CompactBlock50Checks.row14,
  RHFastWindow256CompactBlock50Checks.row15,
  RHFastWindow256CompactBlock50Checks.row16,
  RHFastWindow256CompactBlock50Checks.row17,
  RHFastWindow256CompactBlock50Checks.row18,
  RHFastWindow256CompactBlock50Checks.row19,
  RHFastWindow256CompactBlock50Checks.row20,
  RHFastWindow256CompactBlock50Checks.row21,
  RHFastWindow256CompactBlock50Checks.row22,
  RHFastWindow256CompactBlock50Checks.row23,
  RHFastWindow256CompactBlock50Checks.row24,
  RHFastWindow256CompactBlock50Checks.row25,
  RHFastWindow256CompactBlock50Checks.row26,
  RHFastWindow256CompactBlock50Checks.row27,
  RHFastWindow256CompactBlock50Checks.row28,
  RHFastWindow256CompactBlock50Checks.row29,
  RHFastWindow256CompactBlock50Checks.row30,
  RHFastWindow256CompactBlock50Checks.row31]
#print axioms solution
