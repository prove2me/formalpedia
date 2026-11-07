-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerStabilizer_le_normalizer_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:15.278654+00:00
-- url     : https://prove2.me/submissions/e92086fd-f240-4d7e-85d5-ca4dea89326d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerStabilizer P r level ≤
      Subgroup.normalizer
        (IndexCartwrightStegerImage P r level : Set _) := by
  rw [← IndexCartwrightStegerUnitImage_eq_image]
  exact IndexCartwrightStegerStabilizer_le_normalizer_unitImage P r level
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
