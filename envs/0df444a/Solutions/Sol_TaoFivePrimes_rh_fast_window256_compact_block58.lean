-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block58
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:30:13.062898+00:00
-- url     : https://prove2.me/submissions/0dc4ac2f-794d-4bc9-abf2-89af5ad639d7

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock58Checks
theorem row00 : RHFastWindow256CompactReference.checked (1856+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1856+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1856+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1856+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1856+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1856+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1856+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1856+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1856+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1856+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1856+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1856+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1856+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1856+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1856+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1856+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1856+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1856+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1856+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1856+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1856+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1856+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1856+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1856+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1856+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1856+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1856+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1856+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1856+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1856+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1856+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1856+31)=true := by decide +kernel
end RHFastWindow256CompactBlock58Checks

theorem solution : RHFastWindow256CompactReference.block 1856 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock58Checks.row00,
  RHFastWindow256CompactBlock58Checks.row01,
  RHFastWindow256CompactBlock58Checks.row02,
  RHFastWindow256CompactBlock58Checks.row03,
  RHFastWindow256CompactBlock58Checks.row04,
  RHFastWindow256CompactBlock58Checks.row05,
  RHFastWindow256CompactBlock58Checks.row06,
  RHFastWindow256CompactBlock58Checks.row07,
  RHFastWindow256CompactBlock58Checks.row08,
  RHFastWindow256CompactBlock58Checks.row09,
  RHFastWindow256CompactBlock58Checks.row10,
  RHFastWindow256CompactBlock58Checks.row11,
  RHFastWindow256CompactBlock58Checks.row12,
  RHFastWindow256CompactBlock58Checks.row13,
  RHFastWindow256CompactBlock58Checks.row14,
  RHFastWindow256CompactBlock58Checks.row15,
  RHFastWindow256CompactBlock58Checks.row16,
  RHFastWindow256CompactBlock58Checks.row17,
  RHFastWindow256CompactBlock58Checks.row18,
  RHFastWindow256CompactBlock58Checks.row19,
  RHFastWindow256CompactBlock58Checks.row20,
  RHFastWindow256CompactBlock58Checks.row21,
  RHFastWindow256CompactBlock58Checks.row22,
  RHFastWindow256CompactBlock58Checks.row23,
  RHFastWindow256CompactBlock58Checks.row24,
  RHFastWindow256CompactBlock58Checks.row25,
  RHFastWindow256CompactBlock58Checks.row26,
  RHFastWindow256CompactBlock58Checks.row27,
  RHFastWindow256CompactBlock58Checks.row28,
  RHFastWindow256CompactBlock58Checks.row29,
  RHFastWindow256CompactBlock58Checks.row30,
  RHFastWindow256CompactBlock58Checks.row31]
#print axioms solution
