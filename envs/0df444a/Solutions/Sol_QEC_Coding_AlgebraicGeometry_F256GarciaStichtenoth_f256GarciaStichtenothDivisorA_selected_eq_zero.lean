-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothDivisorA_selected_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:03:47.088952+00:00
-- url     : https://prove2.me/submissions/7941b38f-8c1f-4562-b885-554c1b5ba2c2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_mem_support_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256GarciaStichtenothDivisorA_support_disjoint_D


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    f256GarciaStichtenothDivisorA i (f256GarciaStichtenothSelectedPlace i j) = 0 := by
  classical
  by_contra h
  have hA := Finsupp.mem_support_iff.mpr h
  have hD : f256GarciaStichtenothSelectedPlace i j ∈
      (f256GarciaStichtenothDivisorD i).support := by
    apply Finsupp.mem_support_iff.mpr
    change sourceGaloisClosureSelectedDivisor (i + 2)
      (sourceGaloisClosureSelectedRationalPlace (i + 2) j).place ≠ 0
    erw [sourceGaloisClosureSelectedDivisor_apply]
    norm_num
  exact Finset.disjoint_left.mp (f256GarciaStichtenothDivisorA_support_disjoint_D i) hA hD
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
