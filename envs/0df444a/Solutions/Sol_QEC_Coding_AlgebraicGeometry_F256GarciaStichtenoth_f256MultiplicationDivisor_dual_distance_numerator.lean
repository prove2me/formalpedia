-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_dual_distance_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:46.779046+00:00
-- url     : https://prove2.me/submissions/19c03b0a-47ab-40cc-b487-06f5f88393e3

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
      5 * (Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) + 2 -
        2 * (f256GarciaStichtenothGenus i : ℤ)) := by
  have hl := f256MultiplicationDivisor_degree_lower i
  have hg := f256GarciaStichtenothGenus_fibre_identity i
  have hA := f256GarciaStichtenothDivisorA_degree_pos i
  have hB := f256GarciaStichtenothDivisorB_degree_pos i
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
