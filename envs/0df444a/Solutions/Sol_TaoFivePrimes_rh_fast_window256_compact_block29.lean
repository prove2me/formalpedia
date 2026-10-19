-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block29
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:03:19.979281+00:00
-- url     : https://prove2.me/submissions/c29eda15-6cce-4dab-aece-fa9544d1d129

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock29Checks
theorem row00 : RHFastWindow256CompactReference.checked (928+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (928+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (928+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (928+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (928+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (928+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (928+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (928+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (928+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (928+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (928+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (928+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (928+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (928+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (928+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (928+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (928+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (928+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (928+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (928+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (928+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (928+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (928+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (928+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (928+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (928+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (928+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (928+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (928+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (928+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (928+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (928+31)=true := by decide +kernel
end RHFastWindow256CompactBlock29Checks

theorem solution : RHFastWindow256CompactReference.block 928 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock29Checks.row00,
  RHFastWindow256CompactBlock29Checks.row01,
  RHFastWindow256CompactBlock29Checks.row02,
  RHFastWindow256CompactBlock29Checks.row03,
  RHFastWindow256CompactBlock29Checks.row04,
  RHFastWindow256CompactBlock29Checks.row05,
  RHFastWindow256CompactBlock29Checks.row06,
  RHFastWindow256CompactBlock29Checks.row07,
  RHFastWindow256CompactBlock29Checks.row08,
  RHFastWindow256CompactBlock29Checks.row09,
  RHFastWindow256CompactBlock29Checks.row10,
  RHFastWindow256CompactBlock29Checks.row11,
  RHFastWindow256CompactBlock29Checks.row12,
  RHFastWindow256CompactBlock29Checks.row13,
  RHFastWindow256CompactBlock29Checks.row14,
  RHFastWindow256CompactBlock29Checks.row15,
  RHFastWindow256CompactBlock29Checks.row16,
  RHFastWindow256CompactBlock29Checks.row17,
  RHFastWindow256CompactBlock29Checks.row18,
  RHFastWindow256CompactBlock29Checks.row19,
  RHFastWindow256CompactBlock29Checks.row20,
  RHFastWindow256CompactBlock29Checks.row21,
  RHFastWindow256CompactBlock29Checks.row22,
  RHFastWindow256CompactBlock29Checks.row23,
  RHFastWindow256CompactBlock29Checks.row24,
  RHFastWindow256CompactBlock29Checks.row25,
  RHFastWindow256CompactBlock29Checks.row26,
  RHFastWindow256CompactBlock29Checks.row27,
  RHFastWindow256CompactBlock29Checks.row28,
  RHFastWindow256CompactBlock29Checks.row29,
  RHFastWindow256CompactBlock29Checks.row30,
  RHFastWindow256CompactBlock29Checks.row31]
#print axioms solution
