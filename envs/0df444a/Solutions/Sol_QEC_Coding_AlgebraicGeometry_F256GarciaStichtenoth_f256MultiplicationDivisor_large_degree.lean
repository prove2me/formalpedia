-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_large_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:24:35.605267+00:00
-- url     : https://prove2.me/submissions/529d71e4-0814-4949-a0ac-35bf3c488d6e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_dual_distance_numerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) := by
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
