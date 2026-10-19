-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block37
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:10:52.369854+00:00
-- url     : https://prove2.me/submissions/dd796a55-2cf7-40fe-899c-d92c2ee6f916

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock37Checks
theorem row00 : RHFastWindow256CompactReference.checked (1184+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1184+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1184+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1184+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1184+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1184+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1184+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1184+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1184+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1184+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1184+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1184+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1184+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1184+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1184+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1184+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1184+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1184+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1184+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1184+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1184+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1184+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1184+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1184+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1184+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1184+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1184+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1184+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1184+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1184+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1184+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1184+31)=true := by decide +kernel
end RHFastWindow256CompactBlock37Checks

theorem solution : RHFastWindow256CompactReference.block 1184 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock37Checks.row00,
  RHFastWindow256CompactBlock37Checks.row01,
  RHFastWindow256CompactBlock37Checks.row02,
  RHFastWindow256CompactBlock37Checks.row03,
  RHFastWindow256CompactBlock37Checks.row04,
  RHFastWindow256CompactBlock37Checks.row05,
  RHFastWindow256CompactBlock37Checks.row06,
  RHFastWindow256CompactBlock37Checks.row07,
  RHFastWindow256CompactBlock37Checks.row08,
  RHFastWindow256CompactBlock37Checks.row09,
  RHFastWindow256CompactBlock37Checks.row10,
  RHFastWindow256CompactBlock37Checks.row11,
  RHFastWindow256CompactBlock37Checks.row12,
  RHFastWindow256CompactBlock37Checks.row13,
  RHFastWindow256CompactBlock37Checks.row14,
  RHFastWindow256CompactBlock37Checks.row15,
  RHFastWindow256CompactBlock37Checks.row16,
  RHFastWindow256CompactBlock37Checks.row17,
  RHFastWindow256CompactBlock37Checks.row18,
  RHFastWindow256CompactBlock37Checks.row19,
  RHFastWindow256CompactBlock37Checks.row20,
  RHFastWindow256CompactBlock37Checks.row21,
  RHFastWindow256CompactBlock37Checks.row22,
  RHFastWindow256CompactBlock37Checks.row23,
  RHFastWindow256CompactBlock37Checks.row24,
  RHFastWindow256CompactBlock37Checks.row25,
  RHFastWindow256CompactBlock37Checks.row26,
  RHFastWindow256CompactBlock37Checks.row27,
  RHFastWindow256CompactBlock37Checks.row28,
  RHFastWindow256CompactBlock37Checks.row29,
  RHFastWindow256CompactBlock37Checks.row30,
  RHFastWindow256CompactBlock37Checks.row31]
#print axioms solution
