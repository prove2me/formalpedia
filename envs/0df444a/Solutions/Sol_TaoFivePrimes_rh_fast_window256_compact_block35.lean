-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block35
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:08:49.383982+00:00
-- url     : https://prove2.me/submissions/4460529a-8e2b-4d6c-bdb1-cb7dd77c598c

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock35Checks
theorem row00 : RHFastWindow256CompactReference.checked (1120+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1120+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1120+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1120+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1120+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1120+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1120+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1120+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1120+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1120+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1120+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1120+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1120+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1120+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1120+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1120+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1120+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1120+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1120+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1120+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1120+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1120+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1120+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1120+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1120+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1120+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1120+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1120+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1120+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1120+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1120+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1120+31)=true := by decide +kernel
end RHFastWindow256CompactBlock35Checks

theorem solution : RHFastWindow256CompactReference.block 1120 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock35Checks.row00,
  RHFastWindow256CompactBlock35Checks.row01,
  RHFastWindow256CompactBlock35Checks.row02,
  RHFastWindow256CompactBlock35Checks.row03,
  RHFastWindow256CompactBlock35Checks.row04,
  RHFastWindow256CompactBlock35Checks.row05,
  RHFastWindow256CompactBlock35Checks.row06,
  RHFastWindow256CompactBlock35Checks.row07,
  RHFastWindow256CompactBlock35Checks.row08,
  RHFastWindow256CompactBlock35Checks.row09,
  RHFastWindow256CompactBlock35Checks.row10,
  RHFastWindow256CompactBlock35Checks.row11,
  RHFastWindow256CompactBlock35Checks.row12,
  RHFastWindow256CompactBlock35Checks.row13,
  RHFastWindow256CompactBlock35Checks.row14,
  RHFastWindow256CompactBlock35Checks.row15,
  RHFastWindow256CompactBlock35Checks.row16,
  RHFastWindow256CompactBlock35Checks.row17,
  RHFastWindow256CompactBlock35Checks.row18,
  RHFastWindow256CompactBlock35Checks.row19,
  RHFastWindow256CompactBlock35Checks.row20,
  RHFastWindow256CompactBlock35Checks.row21,
  RHFastWindow256CompactBlock35Checks.row22,
  RHFastWindow256CompactBlock35Checks.row23,
  RHFastWindow256CompactBlock35Checks.row24,
  RHFastWindow256CompactBlock35Checks.row25,
  RHFastWindow256CompactBlock35Checks.row26,
  RHFastWindow256CompactBlock35Checks.row27,
  RHFastWindow256CompactBlock35Checks.row28,
  RHFastWindow256CompactBlock35Checks.row29,
  RHFastWindow256CompactBlock35Checks.row30,
  RHFastWindow256CompactBlock35Checks.row31]
#print axioms solution
