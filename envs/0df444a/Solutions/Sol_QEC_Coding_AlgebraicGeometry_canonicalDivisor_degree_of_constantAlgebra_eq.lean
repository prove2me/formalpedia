-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.canonicalDivisor_degree_of_constantAlgebra_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:35.280513+00:00
-- url     : https://prove2.me/submissions/cc28df86-bab3-4431-b691-2aad1b238843

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_CanonicalDivisor_degree_eq_two_mul_genus_sub_two


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (k F : Type*) [Field k] [Finite k] [Field F]
    [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [κ : Algebra k F] [IsScalarTower k (RatFunc k) F]
    [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    {D : Divisor (GlobalPlace k F)}
    (hD : FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F) D) :
    Divisor.degree (GlobalPlace.residueDegree (κ := κ)) D =
      2 * (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 2 := by
  subst κ
  exact CanonicalDivisor.degree_eq_two_mul_genus_sub_two k F hD
end QEC.Coding.AlgebraicGeometry
