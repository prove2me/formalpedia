-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.three_mul_f256MultiplicationDivisor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:03:00.134419+00:00
-- url     : https://prove2.me/submissions/8444b2aa-6240-4d31-9ed8-e741f0e5c5a4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCoefficient_upper
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothBeta_two_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothCanonicalDivisor_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorA_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorB_nonnegative


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (3 : ℤ) • f256MultiplicationDivisor i ≤
      f256GarciaStichtenothCanonicalDivisor i + f256GarciaStichtenothDivisorD i := by
  rw [f256GarciaStichtenothCanonicalDivisor_eq, sub_add_cancel]
  intro P
  change 3 * (f256MultiplicationCoefficient i * f256GarciaStichtenothDivisorA i P) ≤
    (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) * f256GarciaStichtenothDivisorA i P +
      ((f256GarciaStichtenothBeta i : ℤ) - 2) * f256GarciaStichtenothDivisorB i P
  have hA := f256GarciaStichtenothDivisorA_nonnegative i P
  have hB := f256GarciaStichtenothDivisorB_nonnegative i P
  have hβ : (0 : ℤ) ≤ (f256GarciaStichtenothBeta i : ℤ) - 2 := by
    have h := f256GarciaStichtenothBeta_two_le i
    omega
  have hs := mul_le_mul_of_nonneg_right (f256MultiplicationCoefficient_upper i) hA
  have hb := mul_nonneg hβ hB
  nlinarith
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
