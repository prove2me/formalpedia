-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexWitnessGL_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:41:58.848875+00:00
-- url     : https://prove2.me/submissions/0ae94d84-82a5-4e2e-a3e2-15ad9c95d73a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generalLinear_det_surjective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Matrix.GeneralLinearGroup.det (indexWitnessGL P r level) =
      indexRatioUnit P r level :=
  Classical.choose_spec
    (ProjectiveIndex.generalLinear_det_surjective
      (Fin r.matrixRank) (ResidueField P r level)
      (indexRatioUnit P r level))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
