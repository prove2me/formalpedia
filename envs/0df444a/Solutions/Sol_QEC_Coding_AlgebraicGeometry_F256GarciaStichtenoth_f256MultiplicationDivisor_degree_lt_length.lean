-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree_lt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:18:49.782221+00:00
-- url     : https://prove2.me/submissions/059d0020-9d3c-4422-96d2-0bd3f40f5b3b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_upper
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) <
      f256GarciaStichtenothLength i := by
  have hu := f256MultiplicationDivisor_degree_upper i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
