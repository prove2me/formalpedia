-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block48
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:21:21.773797+00:00
-- url     : https://prove2.me/submissions/6b03af84-2271-49e6-ab34-f6a7f2e025c4

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock48Checks
theorem row00 : RHFastWindow256CompactReference.checked (1536+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1536+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1536+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1536+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1536+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1536+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1536+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1536+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1536+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1536+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1536+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1536+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1536+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1536+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1536+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1536+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1536+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1536+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1536+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1536+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1536+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1536+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1536+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1536+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1536+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1536+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1536+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1536+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1536+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1536+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1536+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1536+31)=true := by decide +kernel
end RHFastWindow256CompactBlock48Checks

theorem solution : RHFastWindow256CompactReference.block 1536 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock48Checks.row00,
  RHFastWindow256CompactBlock48Checks.row01,
  RHFastWindow256CompactBlock48Checks.row02,
  RHFastWindow256CompactBlock48Checks.row03,
  RHFastWindow256CompactBlock48Checks.row04,
  RHFastWindow256CompactBlock48Checks.row05,
  RHFastWindow256CompactBlock48Checks.row06,
  RHFastWindow256CompactBlock48Checks.row07,
  RHFastWindow256CompactBlock48Checks.row08,
  RHFastWindow256CompactBlock48Checks.row09,
  RHFastWindow256CompactBlock48Checks.row10,
  RHFastWindow256CompactBlock48Checks.row11,
  RHFastWindow256CompactBlock48Checks.row12,
  RHFastWindow256CompactBlock48Checks.row13,
  RHFastWindow256CompactBlock48Checks.row14,
  RHFastWindow256CompactBlock48Checks.row15,
  RHFastWindow256CompactBlock48Checks.row16,
  RHFastWindow256CompactBlock48Checks.row17,
  RHFastWindow256CompactBlock48Checks.row18,
  RHFastWindow256CompactBlock48Checks.row19,
  RHFastWindow256CompactBlock48Checks.row20,
  RHFastWindow256CompactBlock48Checks.row21,
  RHFastWindow256CompactBlock48Checks.row22,
  RHFastWindow256CompactBlock48Checks.row23,
  RHFastWindow256CompactBlock48Checks.row24,
  RHFastWindow256CompactBlock48Checks.row25,
  RHFastWindow256CompactBlock48Checks.row26,
  RHFastWindow256CompactBlock48Checks.row27,
  RHFastWindow256CompactBlock48Checks.row28,
  RHFastWindow256CompactBlock48Checks.row29,
  RHFastWindow256CompactBlock48Checks.row30,
  RHFastWindow256CompactBlock48Checks.row31]
#print axioms solution
