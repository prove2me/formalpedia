-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block60
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:33:19.217357+00:00
-- url     : https://prove2.me/submissions/767abc09-1713-4b56-86e6-2fba8d69148d

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock60Checks
theorem row00 : RHFastWindow256CompactReference.checked (1920+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1920+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1920+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1920+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1920+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1920+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1920+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1920+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1920+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1920+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1920+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1920+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1920+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1920+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1920+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1920+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1920+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1920+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1920+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1920+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1920+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1920+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1920+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1920+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1920+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1920+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1920+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1920+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1920+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1920+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1920+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1920+31)=true := by decide +kernel
end RHFastWindow256CompactBlock60Checks

theorem solution : RHFastWindow256CompactReference.block 1920 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock60Checks.row00,
  RHFastWindow256CompactBlock60Checks.row01,
  RHFastWindow256CompactBlock60Checks.row02,
  RHFastWindow256CompactBlock60Checks.row03,
  RHFastWindow256CompactBlock60Checks.row04,
  RHFastWindow256CompactBlock60Checks.row05,
  RHFastWindow256CompactBlock60Checks.row06,
  RHFastWindow256CompactBlock60Checks.row07,
  RHFastWindow256CompactBlock60Checks.row08,
  RHFastWindow256CompactBlock60Checks.row09,
  RHFastWindow256CompactBlock60Checks.row10,
  RHFastWindow256CompactBlock60Checks.row11,
  RHFastWindow256CompactBlock60Checks.row12,
  RHFastWindow256CompactBlock60Checks.row13,
  RHFastWindow256CompactBlock60Checks.row14,
  RHFastWindow256CompactBlock60Checks.row15,
  RHFastWindow256CompactBlock60Checks.row16,
  RHFastWindow256CompactBlock60Checks.row17,
  RHFastWindow256CompactBlock60Checks.row18,
  RHFastWindow256CompactBlock60Checks.row19,
  RHFastWindow256CompactBlock60Checks.row20,
  RHFastWindow256CompactBlock60Checks.row21,
  RHFastWindow256CompactBlock60Checks.row22,
  RHFastWindow256CompactBlock60Checks.row23,
  RHFastWindow256CompactBlock60Checks.row24,
  RHFastWindow256CompactBlock60Checks.row25,
  RHFastWindow256CompactBlock60Checks.row26,
  RHFastWindow256CompactBlock60Checks.row27,
  RHFastWindow256CompactBlock60Checks.row28,
  RHFastWindow256CompactBlock60Checks.row29,
  RHFastWindow256CompactBlock60Checks.row30,
  RHFastWindow256CompactBlock60Checks.row31]
#print axioms solution
