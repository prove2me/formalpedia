-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceCoordinates_window_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:38:43.001861+00:00
-- url     : https://prove2.me/submissions/0f99c985-eef1-4ca5-8497-ba10d08e9f96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalCoordinateCells
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceRecursion_fieldRange_sup_coordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinateWindow_congr
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coordinateWindow_map


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    coordinateWindow (sourceCoordinates m) 0 m = ⊤ := by
  induction m with
  | zero => exact RatFunc.adjoin_X
  | succ m ih =>
      have hp : coordinateWindow (sourceCoordinates (m + 1)) 0 m =
          (coordinateWindow (sourceCoordinates m) 0 m).map (sourceRecursionEmbedding m) := by
        rw [coordinateWindow_map]
        apply coordinateWindow_congr
        intro i hi
        exact sourceCoordinates_succ_of_le m (0 + i) (by omega)
      rw [coordinateWindow, Nat.zero_add, sourceCoordinates_last, hp, ih,
        ← AlgHom.fieldRange_eq_map]
      exact sourceRecursion_fieldRange_sup_coordinate m
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
