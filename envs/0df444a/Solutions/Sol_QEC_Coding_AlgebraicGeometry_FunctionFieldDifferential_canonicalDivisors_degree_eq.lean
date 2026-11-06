-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:41.209594+00:00
-- url     : https://prove2.me/submissions/188ecb4b-b272-496e-95f5-eec100f3c3dd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_canonicalDivisors_differ_by_principal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) K =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) L := by
  rcases canonicalDivisors_differ_by_principal (k := k) (F := F) hK hL with ⟨u, hL⟩
  rw [hL, Divisor.degree_add, GlobalPlace.principalDivisor_degree_zero, zero_add]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
