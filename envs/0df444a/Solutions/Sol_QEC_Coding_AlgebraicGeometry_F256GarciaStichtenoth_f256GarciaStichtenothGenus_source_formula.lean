-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_source_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:51.367612+00:00
-- url     : https://prove2.me/submissions/bf6f15e4-476a-4aa5-8d47-009f9c3869a8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureGenus_eq_source_formula


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (f256GarciaStichtenothGenus i : ℚ) = 1 + (f256GarciaStichtenothLength i : ℚ) / 15 *
      (1 - 1 / (f256GarciaStichtenothAlpha i : ℚ) - 1 / (f256GarciaStichtenothBeta i : ℚ)) :=
  sourceClosureGenus_eq_source_formula (i + 2)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
