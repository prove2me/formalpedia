-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block21
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:56:26.807866+00:00
-- url     : https://prove2.me/submissions/a66dd454-a6cf-466f-bc41-f5a92c8af87a

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock21Checks
theorem row00 : RHFastWindow256CompactReference.checked (672+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (672+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (672+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (672+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (672+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (672+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (672+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (672+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (672+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (672+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (672+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (672+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (672+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (672+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (672+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (672+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (672+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (672+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (672+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (672+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (672+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (672+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (672+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (672+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (672+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (672+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (672+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (672+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (672+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (672+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (672+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (672+31)=true := by decide +kernel
end RHFastWindow256CompactBlock21Checks

theorem solution : RHFastWindow256CompactReference.block 672 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock21Checks.row00,
  RHFastWindow256CompactBlock21Checks.row01,
  RHFastWindow256CompactBlock21Checks.row02,
  RHFastWindow256CompactBlock21Checks.row03,
  RHFastWindow256CompactBlock21Checks.row04,
  RHFastWindow256CompactBlock21Checks.row05,
  RHFastWindow256CompactBlock21Checks.row06,
  RHFastWindow256CompactBlock21Checks.row07,
  RHFastWindow256CompactBlock21Checks.row08,
  RHFastWindow256CompactBlock21Checks.row09,
  RHFastWindow256CompactBlock21Checks.row10,
  RHFastWindow256CompactBlock21Checks.row11,
  RHFastWindow256CompactBlock21Checks.row12,
  RHFastWindow256CompactBlock21Checks.row13,
  RHFastWindow256CompactBlock21Checks.row14,
  RHFastWindow256CompactBlock21Checks.row15,
  RHFastWindow256CompactBlock21Checks.row16,
  RHFastWindow256CompactBlock21Checks.row17,
  RHFastWindow256CompactBlock21Checks.row18,
  RHFastWindow256CompactBlock21Checks.row19,
  RHFastWindow256CompactBlock21Checks.row20,
  RHFastWindow256CompactBlock21Checks.row21,
  RHFastWindow256CompactBlock21Checks.row22,
  RHFastWindow256CompactBlock21Checks.row23,
  RHFastWindow256CompactBlock21Checks.row24,
  RHFastWindow256CompactBlock21Checks.row25,
  RHFastWindow256CompactBlock21Checks.row26,
  RHFastWindow256CompactBlock21Checks.row27,
  RHFastWindow256CompactBlock21Checks.row28,
  RHFastWindow256CompactBlock21Checks.row29,
  RHFastWindow256CompactBlock21Checks.row30,
  RHFastWindow256CompactBlock21Checks.row31]
#print axioms solution
