-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256MultiplicationDivisor_degree_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:09:26.809877+00:00
-- url     : https://prove2.me/submissions/52bcbecf-d942-4206-b741-77d8343228f1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationCoefficient_lower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothAlpha_mul_degree_divisorA
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorA_degree_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothLength_fifteen_dvd

section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
private theorem fifteen_mul_alpha_fibre_degree (i : ℕ) :
    15 * ((f256GarciaStichtenothAlpha i : ℤ) *
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i)) =
        f256GarciaStichtenothLength i := by
  rw [f256GarciaStichtenothAlpha_mul_degree_divisorA]
  exact_mod_cast Nat.mul_div_cancel' (f256GarciaStichtenothLength_fifteen_dvd i)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    5 * (f256GarciaStichtenothLength i : ℤ) ≤
      15 * Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i) := by
  rw [f256MultiplicationDivisor_degree]
  have h := mul_le_mul_of_nonneg_right (f256MultiplicationCoefficient_lower i)
    (le_of_lt (f256GarciaStichtenothDivisorA_degree_pos i))
  have hA := fifteen_mul_alpha_fibre_degree i
  nlinarith
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
