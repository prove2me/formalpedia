-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.agEvaluation_le_dual_of_residue_of_constantAlgebra_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:41:21.448778+00:00
-- url     : https://prove2.me/submissions/935d2927-b232-4f20-9974-7a737628f792

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_le_dual_of_residue


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
omit [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    [IsScalarTower k (RatFunc k) F]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ FunctionFieldDifferential.differentialDivisor eta heta + evaluationDivisor Q) :
    (agEvaluationCode H Q hH).carrier ≤ (agEvaluationCode G Q hG).dual.carrier := by
  subst κ
  exact agEvaluation_le_dual_of_residue k F G H Q hQ hG hH eta heta etaAt hAt hres hGH
end QEC.Coding.AlgebraicGeometry
