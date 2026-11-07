-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexWitness_eq_PGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:48.92219+00:00
-- url     : https://prove2.me/submissions/e58b275d-4939-4baa-9a9f-4f51815b8888

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generatedProjectiveImage_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_indexWitness_orderOf

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    PSL P r level ⊔ Subgroup.zpowers (indexWitness P r level) = ⊤ := by
  exact ProjectiveIndex.generatedProjectiveImage_eq_top
      (Fin r.matrixRank) (ResidueField P r level)
      (indexWitness P r level)
      (residueProjectiveDetClass_indexWitness_orderOf P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
