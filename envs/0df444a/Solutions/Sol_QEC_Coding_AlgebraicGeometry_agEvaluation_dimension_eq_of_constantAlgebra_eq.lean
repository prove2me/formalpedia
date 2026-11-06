-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_dimension_eq_of_constantAlgebra_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:41:09.537195+00:00
-- url     : https://prove2.me/submissions/6192ddc7-22b1-4413-bddb-ba54b7f3fe83

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dimension_eq_of_large_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
variable [κ : Algebra k F]
variable [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
variable {ι : Type*} [Fintype ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G)
    (hsmall : Divisor.degree GlobalPlace.residueDegree G < Fintype.card ι) :
    (Dimension (agEvaluationCode G Q hG) : ℤ) =
      Divisor.degree GlobalPlace.residueDegree G + 1 -
        (GlobalPlace.functionFieldGenus
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) := by
  subst κ
  exact agEvaluation_dimension_eq_of_large_degree k F G Q hQ hG hlarge hsmall
end QEC.Coding.AlgebraicGeometry
