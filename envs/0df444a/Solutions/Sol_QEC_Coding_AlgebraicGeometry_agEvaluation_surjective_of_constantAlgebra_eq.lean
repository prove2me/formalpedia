-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_surjective_of_constantAlgebra_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:41:22.293972+00:00
-- url     : https://prove2.me/submissions/4e9b285f-3360-4cb3-ac70-883b3ad0eff6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_surjective_of_sub_degree


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
        Divisor.degree GlobalPlace.residueDegree G - Fintype.card ι) :
    Function.Surjective (agEvaluationLinearMap G Q hG) := by
  subst κ
  exact agEvaluation_surjective_of_sub_degree k F G Q hQ hG hlarge
end QEC.Coding.AlgebraicGeometry
