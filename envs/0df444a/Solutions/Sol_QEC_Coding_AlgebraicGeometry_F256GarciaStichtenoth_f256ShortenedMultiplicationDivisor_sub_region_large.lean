-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256ShortenedMultiplicationDivisor_sub_region_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:32:36.024572+00:00
-- url     : https://prove2.me/submissions/e8380783-3224-4692-bbce-de50a3b497d4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_two_hundred_forty_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_dual_distance_numerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ShortenedMultiplicationDivisor_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (S : Finset (F256MultiplicationRetained i))
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i) :
    2 * (f256GarciaStichtenothGenus i : ℤ) - 1 ≤
      Divisor.degree GlobalPlace.residueDegree (f256ShortenedMultiplicationDivisor i) -
        Fintype.card S := by
  rw [f256ShortenedMultiplicationDivisor_degree, Fintype.card_coe]
  have h := f256MultiplicationDivisor_dual_distance_numerator i
  have hn := f256GarciaStichtenothLength_two_hundred_forty_le i
  unfold f256MultiplicationLogicalCount at *
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
