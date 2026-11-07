-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothGenus_fibre_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:09:26.012072+00:00
-- url     : https://prove2.me/submissions/d118b93e-e8d2-4143-bc3a-a0ac32f907d0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWRelativeDegree_mul_fifteen


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    15 * ((f256GarciaStichtenothGenus i : ℤ) - 1 +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) +
      Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i)) =
        f256GarciaStichtenothLength i := by
  have hg := sourceClosureGenus_eq_relativeDegree_sub_fibreDegrees (i + 2)
  have hn : (15 : ℤ) * (sourceGaloisWRelativeDegree (i + 2) : ℤ) =
      f256GarciaStichtenothLength i := by
    exact_mod_cast sourceGaloisWRelativeDegree_mul_fifteen (i + 2)
  change (f256GarciaStichtenothGenus i : ℤ) = 1 +
    (sourceGaloisWRelativeDegree (i + 2) : ℤ) -
    Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorA i) -
    Divisor.degree GlobalPlace.residueDegree (f256GarciaStichtenothDivisorB i) at hg
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
