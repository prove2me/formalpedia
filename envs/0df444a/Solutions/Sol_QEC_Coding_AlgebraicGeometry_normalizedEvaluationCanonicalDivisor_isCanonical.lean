-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.normalizedEvaluationCanonicalDivisor_isCanonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:16:40.475566+00:00
-- url     : https://prove2.me/submissions/f6d7fd57-f82a-4f52-b353-ed05af44ff90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityAlgebra
attribute [local instance] agCodeDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityScalarTower
attribute [local instance] agCodeDualityScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityFiniteDimensional
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
variable [Nonempty ι]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F)
      (normalizedEvaluationCanonicalDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) :=
  FunctionFieldDifferential.differentialDivisor_isCanonical
    (k := k) (F := F)
    (normalizedEvaluationDifferential
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
    (normalizedEvaluationDifferential_ne_zero
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ)
end QEC.Coding.AlgebraicGeometry
