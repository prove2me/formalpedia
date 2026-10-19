-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block44
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:17:44.569725+00:00
-- url     : https://prove2.me/submissions/fd9c3ee4-ea3e-4beb-a0a6-03d9952b137e

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock44Checks
theorem row00 : RHFastWindow256CompactReference.checked (1408+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1408+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1408+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1408+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1408+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1408+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1408+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1408+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1408+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1408+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1408+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1408+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1408+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1408+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1408+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1408+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1408+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1408+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1408+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1408+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1408+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1408+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1408+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1408+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1408+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1408+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1408+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1408+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1408+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1408+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1408+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1408+31)=true := by decide +kernel
end RHFastWindow256CompactBlock44Checks

theorem solution : RHFastWindow256CompactReference.block 1408 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock44Checks.row00,
  RHFastWindow256CompactBlock44Checks.row01,
  RHFastWindow256CompactBlock44Checks.row02,
  RHFastWindow256CompactBlock44Checks.row03,
  RHFastWindow256CompactBlock44Checks.row04,
  RHFastWindow256CompactBlock44Checks.row05,
  RHFastWindow256CompactBlock44Checks.row06,
  RHFastWindow256CompactBlock44Checks.row07,
  RHFastWindow256CompactBlock44Checks.row08,
  RHFastWindow256CompactBlock44Checks.row09,
  RHFastWindow256CompactBlock44Checks.row10,
  RHFastWindow256CompactBlock44Checks.row11,
  RHFastWindow256CompactBlock44Checks.row12,
  RHFastWindow256CompactBlock44Checks.row13,
  RHFastWindow256CompactBlock44Checks.row14,
  RHFastWindow256CompactBlock44Checks.row15,
  RHFastWindow256CompactBlock44Checks.row16,
  RHFastWindow256CompactBlock44Checks.row17,
  RHFastWindow256CompactBlock44Checks.row18,
  RHFastWindow256CompactBlock44Checks.row19,
  RHFastWindow256CompactBlock44Checks.row20,
  RHFastWindow256CompactBlock44Checks.row21,
  RHFastWindow256CompactBlock44Checks.row22,
  RHFastWindow256CompactBlock44Checks.row23,
  RHFastWindow256CompactBlock44Checks.row24,
  RHFastWindow256CompactBlock44Checks.row25,
  RHFastWindow256CompactBlock44Checks.row26,
  RHFastWindow256CompactBlock44Checks.row27,
  RHFastWindow256CompactBlock44Checks.row28,
  RHFastWindow256CompactBlock44Checks.row29,
  RHFastWindow256CompactBlock44Checks.row30,
  RHFastWindow256CompactBlock44Checks.row31]
#print axioms solution
