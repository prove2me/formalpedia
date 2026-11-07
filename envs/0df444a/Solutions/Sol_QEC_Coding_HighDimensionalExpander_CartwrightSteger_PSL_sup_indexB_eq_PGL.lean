-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexB_eq_PGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:05.36565+00:00
-- url     : https://prove2.me/submissions/d0fce75f-3223-4e68-91d8-c065dd3bd758

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueProjectiveDetClass_indexB_orderOf
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_generatedProjectiveImage_eq_top


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    PSL P r level ⊔ Subgroup.zpowers (indexB P r level) = ⊤ := by
  exact ProjectiveIndex.generatedProjectiveImage_eq_top
      (Fin r.matrixRank) (ResidueField P r level)
      (indexB P r level)
      (residueProjectiveDetClass_indexB_orderOf P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
