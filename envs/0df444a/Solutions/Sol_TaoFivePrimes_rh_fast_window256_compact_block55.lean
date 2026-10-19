-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_compact_block55
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T12:27:46.303636+00:00
-- url     : https://prove2.me/submissions/6a7840cb-303c-4bfe-a827-367562eff7c6

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace RHFastWindow256CompactBlock55Checks
theorem row00 : RHFastWindow256CompactReference.checked (1760+0)=true := by decide +kernel
theorem row01 : RHFastWindow256CompactReference.checked (1760+1)=true := by decide +kernel
theorem row02 : RHFastWindow256CompactReference.checked (1760+2)=true := by decide +kernel
theorem row03 : RHFastWindow256CompactReference.checked (1760+3)=true := by decide +kernel
theorem row04 : RHFastWindow256CompactReference.checked (1760+4)=true := by decide +kernel
theorem row05 : RHFastWindow256CompactReference.checked (1760+5)=true := by decide +kernel
theorem row06 : RHFastWindow256CompactReference.checked (1760+6)=true := by decide +kernel
theorem row07 : RHFastWindow256CompactReference.checked (1760+7)=true := by decide +kernel
theorem row08 : RHFastWindow256CompactReference.checked (1760+8)=true := by decide +kernel
theorem row09 : RHFastWindow256CompactReference.checked (1760+9)=true := by decide +kernel
theorem row10 : RHFastWindow256CompactReference.checked (1760+10)=true := by decide +kernel
theorem row11 : RHFastWindow256CompactReference.checked (1760+11)=true := by decide +kernel
theorem row12 : RHFastWindow256CompactReference.checked (1760+12)=true := by decide +kernel
theorem row13 : RHFastWindow256CompactReference.checked (1760+13)=true := by decide +kernel
theorem row14 : RHFastWindow256CompactReference.checked (1760+14)=true := by decide +kernel
theorem row15 : RHFastWindow256CompactReference.checked (1760+15)=true := by decide +kernel
theorem row16 : RHFastWindow256CompactReference.checked (1760+16)=true := by decide +kernel
theorem row17 : RHFastWindow256CompactReference.checked (1760+17)=true := by decide +kernel
theorem row18 : RHFastWindow256CompactReference.checked (1760+18)=true := by decide +kernel
theorem row19 : RHFastWindow256CompactReference.checked (1760+19)=true := by decide +kernel
theorem row20 : RHFastWindow256CompactReference.checked (1760+20)=true := by decide +kernel
theorem row21 : RHFastWindow256CompactReference.checked (1760+21)=true := by decide +kernel
theorem row22 : RHFastWindow256CompactReference.checked (1760+22)=true := by decide +kernel
theorem row23 : RHFastWindow256CompactReference.checked (1760+23)=true := by decide +kernel
theorem row24 : RHFastWindow256CompactReference.checked (1760+24)=true := by decide +kernel
theorem row25 : RHFastWindow256CompactReference.checked (1760+25)=true := by decide +kernel
theorem row26 : RHFastWindow256CompactReference.checked (1760+26)=true := by decide +kernel
theorem row27 : RHFastWindow256CompactReference.checked (1760+27)=true := by decide +kernel
theorem row28 : RHFastWindow256CompactReference.checked (1760+28)=true := by decide +kernel
theorem row29 : RHFastWindow256CompactReference.checked (1760+29)=true := by decide +kernel
theorem row30 : RHFastWindow256CompactReference.checked (1760+30)=true := by decide +kernel
theorem row31 : RHFastWindow256CompactReference.checked (1760+31)=true := by decide +kernel
end RHFastWindow256CompactBlock55Checks

theorem solution : RHFastWindow256CompactReference.block 1760 32=true := by
 simp only [RHFastWindow256CompactReference.block,List.range_succ,List.range_zero,
  List.all_append,List.all_cons,List.all_nil,Bool.and_true,
  RHFastWindow256CompactBlock55Checks.row00,
  RHFastWindow256CompactBlock55Checks.row01,
  RHFastWindow256CompactBlock55Checks.row02,
  RHFastWindow256CompactBlock55Checks.row03,
  RHFastWindow256CompactBlock55Checks.row04,
  RHFastWindow256CompactBlock55Checks.row05,
  RHFastWindow256CompactBlock55Checks.row06,
  RHFastWindow256CompactBlock55Checks.row07,
  RHFastWindow256CompactBlock55Checks.row08,
  RHFastWindow256CompactBlock55Checks.row09,
  RHFastWindow256CompactBlock55Checks.row10,
  RHFastWindow256CompactBlock55Checks.row11,
  RHFastWindow256CompactBlock55Checks.row12,
  RHFastWindow256CompactBlock55Checks.row13,
  RHFastWindow256CompactBlock55Checks.row14,
  RHFastWindow256CompactBlock55Checks.row15,
  RHFastWindow256CompactBlock55Checks.row16,
  RHFastWindow256CompactBlock55Checks.row17,
  RHFastWindow256CompactBlock55Checks.row18,
  RHFastWindow256CompactBlock55Checks.row19,
  RHFastWindow256CompactBlock55Checks.row20,
  RHFastWindow256CompactBlock55Checks.row21,
  RHFastWindow256CompactBlock55Checks.row22,
  RHFastWindow256CompactBlock55Checks.row23,
  RHFastWindow256CompactBlock55Checks.row24,
  RHFastWindow256CompactBlock55Checks.row25,
  RHFastWindow256CompactBlock55Checks.row26,
  RHFastWindow256CompactBlock55Checks.row27,
  RHFastWindow256CompactBlock55Checks.row28,
  RHFastWindow256CompactBlock55Checks.row29,
  RHFastWindow256CompactBlock55Checks.row30,
  RHFastWindow256CompactBlock55Checks.row31]
#print axioms solution
