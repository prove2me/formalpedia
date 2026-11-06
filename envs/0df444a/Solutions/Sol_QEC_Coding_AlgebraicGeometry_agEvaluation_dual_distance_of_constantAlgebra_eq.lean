-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_dual_distance_of_constantAlgebra_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:41:17.835196+00:00
-- url     : https://prove2.me/submissions/b0cba2b7-36eb-4695-81e8-ad73f29634b2

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_dual_distance_lower_bound


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
    [Nonempty ι] [DecidableEq k] [DecidableEq ι]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0)
    (hlarge : 2 * (GlobalPlace.functionFieldGenus
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ) - 1 ≤
        Divisor.degree GlobalPlace.residueDegree G)
    (hsmall : Divisor.degree GlobalPlace.residueDegree G < Fintype.card ι) :
    (Int.toNat (Divisor.degree GlobalPlace.residueDegree G + 2 -
      2 * (GlobalPlace.functionFieldGenus
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F : ℤ)) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (agEvaluationCode G Q hG).dual := by
  subst κ
  exact agEvaluation_dual_distance_lower_bound k F G Q hQ hG hlarge hsmall
end QEC.Coding.AlgebraicGeometry
