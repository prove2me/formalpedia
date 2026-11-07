-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_IndexCartwrightStegerColorZero_iff_mem_PSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:17.413486+00:00
-- url     : https://prove2.me/submissions/167da6fe-0862-4a56-a327-b54b1d0daf16

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ker_residueProjectiveDetClass_eq_PSL


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : IndexCartwrightStegerImage P r level) :
    g ∈ IndexCartwrightStegerColorZero P r level ↔
      (g : PGL P r level) ∈ PSL P r level := by
  change (g : PGL P r level) ∈
      (residueProjectiveDetClass P r level).ker ↔
    (g : PGL P r level) ∈ PSL P r level
  rw [ker_residueProjectiveDetClass_eq_PSL]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
