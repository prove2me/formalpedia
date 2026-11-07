-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_ngu24_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:37:41.052066+00:00
-- url     : https://prove2.me/submissions/6713cf66-73ed-4feb-ab83-6d862309db55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothAlpha_two_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothBeta_two_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothGenus_source_formula

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    15 * (f256GarciaStichtenothAlpha i : ℤ) * f256GarciaStichtenothBeta i *
      ((f256GarciaStichtenothGenus i : ℤ) - 1) =
      f256GarciaStichtenothLength i * ((f256GarciaStichtenothAlpha i : ℤ) *
        f256GarciaStichtenothBeta i - f256GarciaStichtenothAlpha i - f256GarciaStichtenothBeta i) := by
  have ha : (f256GarciaStichtenothAlpha i : ℚ) ≠ 0 := by
    exact_mod_cast (by have h := f256GarciaStichtenothAlpha_two_le i; omega : f256GarciaStichtenothAlpha i ≠ 0)
  have hb : (f256GarciaStichtenothBeta i : ℚ) ≠ 0 := by
    exact_mod_cast (by have h := f256GarciaStichtenothBeta_two_le i; omega : f256GarciaStichtenothBeta i ≠ 0)
  have h : (15 : ℚ) * f256GarciaStichtenothAlpha i * f256GarciaStichtenothBeta i *
      ((f256GarciaStichtenothGenus i : ℚ) - 1) =
      f256GarciaStichtenothLength i * ((f256GarciaStichtenothAlpha i : ℚ) *
        f256GarciaStichtenothBeta i - f256GarciaStichtenothAlpha i - f256GarciaStichtenothBeta i) := by
    rw [f256GarciaStichtenothGenus_source_formula]
    field_simp
    ring
  exact_mod_cast h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
