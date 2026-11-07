-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothBeta_mul_degree_divisorB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:58:01.351033+00:00
-- url     : https://prove2.me/submissions/c13830a2-e431-4da2-85c3-7cadcc8b22d6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree_eq_length_div


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (f256GarciaStichtenothBeta i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) =
        (f256GarciaStichtenothLength i / 15 : ℕ) :=
  sourceGaloisWInfinityRamificationIndex_mul_fibreDivisor_degree_eq_length_div (i + 2)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
