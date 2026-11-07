-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorB_degree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:04:21.832211+00:00
-- url     : https://prove2.me/submissions/210d2425-5172-42c4-86b1-433758b2b163

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_div_fifteen_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothBeta_mul_degree_divisorB

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    0 < Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) := by
  have hp : (0 : ℤ) < (f256GarciaStichtenothLength i / 15 : ℕ) := by
    exact_mod_cast f256GarciaStichtenothLength_div_fifteen_pos i
  by_contra hn
  have h := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg (f256GarciaStichtenothBeta i))
    (le_of_not_gt hn)
  rw [f256GarciaStichtenothBeta_mul_degree_divisorB] at h
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
