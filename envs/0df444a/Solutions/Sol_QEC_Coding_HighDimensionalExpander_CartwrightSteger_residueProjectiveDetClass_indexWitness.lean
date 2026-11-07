-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueProjectiveDetClass_indexWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:00.615514+00:00
-- url     : https://prove2.me/submissions/957b33ce-60c8-41de-a0f3-e198c5ef9c72

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexWitnessGL_det

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueProjectiveDetClass P r level (indexWitness P r level) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) := by
  rw [indexWitness, residueProjectiveDetClass]
  change QuotientGroup.mk' _
      (Matrix.GeneralLinearGroup.det (indexWitnessGL P r level)) = _
  rw [indexWitnessGL_det]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
