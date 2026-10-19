-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block27
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:01:29.181007+00:00
-- url     : https://prove2.me/submissions/6ae259fb-3e61-4cee-8744-2a9e0570b258

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock27Checks
theorem row00 : RHFastWindow256CompactReference.checked (864+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (864+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (864+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (864+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (864+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (864+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (864+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (864+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (864+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (864+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (864+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (864+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (864+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (864+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (864+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (864+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (864+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (864+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (864+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (864+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (864+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (864+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (864+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (864+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (864+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (864+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (864+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (864+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (864+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (864+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (864+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (864+31)=true := by decide +kernel
end RHFastWindow256CompactBlock27Checks

theorem solution : RHFastWindow256CompactReference.block 864 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock27Checks.row00,
  RHFastWindow256CompactBlock27Checks.row01,
  RHFastWindow256CompactBlock27Checks.row02,
  RHFastWindow256CompactBlock27Checks.row03,
  RHFastWindow256CompactBlock27Checks.row04,
  RHFastWindow256CompactBlock27Checks.row05,
  RHFastWindow256CompactBlock27Checks.row06,
  RHFastWindow256CompactBlock27Checks.row07,
  RHFastWindow256CompactBlock27Checks.row08,
  RHFastWindow256CompactBlock27Checks.row09,
  RHFastWindow256CompactBlock27Checks.row10,
  RHFastWindow256CompactBlock27Checks.row11,
  RHFastWindow256CompactBlock27Checks.row12,
  RHFastWindow256CompactBlock27Checks.row13,
  RHFastWindow256CompactBlock27Checks.row14,
  RHFastWindow256CompactBlock27Checks.row15,
  RHFastWindow256CompactBlock27Checks.row16,
  RHFastWindow256CompactBlock27Checks.row17,
  RHFastWindow256CompactBlock27Checks.row18,
  RHFastWindow256CompactBlock27Checks.row19,
  RHFastWindow256CompactBlock27Checks.row20,
  RHFastWindow256CompactBlock27Checks.row21,
  RHFastWindow256CompactBlock27Checks.row22,
  RHFastWindow256CompactBlock27Checks.row23,
  RHFastWindow256CompactBlock27Checks.row24,
  RHFastWindow256CompactBlock27Checks.row25,
  RHFastWindow256CompactBlock27Checks.row26,
  RHFastWindow256CompactBlock27Checks.row27,
  RHFastWindow256CompactBlock27Checks.row28,
  RHFastWindow256CompactBlock27Checks.row29,
  RHFastWindow256CompactBlock27Checks.row30,
  RHFastWindow256CompactBlock27Checks.row31]
#print axioms solution
