-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_dimension_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:52.199445+00:00
-- url     : https://prove2.me/submissions/0338eb39-7ff9-4674-b05f-b6e45dd65e6f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothGenus_fibre_identity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_lower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorA_degree_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorB_degree_pos


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (f256GarciaStichtenothLength i : ℤ) ≤
      4 * (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 1 -
        f256GarciaStichtenothGenus i) := by
  have hl := f256MultiplicationDivisor_degree_lower i
  have hg := f256GarciaStichtenothGenus_fibre_identity i
  have hA := f256GarciaStichtenothDivisorA_degree_pos i
  have hB := f256GarciaStichtenothDivisorB_degree_pos i
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
