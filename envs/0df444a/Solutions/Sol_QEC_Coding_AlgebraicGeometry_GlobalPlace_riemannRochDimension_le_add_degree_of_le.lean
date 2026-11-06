-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_le_add_degree_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:56:42.029234+00:00
-- url     : https://prove2.me/submissions/6a1872bd-69e9-468d-8e0f-26811d77f371

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_add_nonnegative_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementAlgebra
attribute [local instance] riemannRochEffectiveIncrementAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochEffectiveIncrementScalarTower
attribute [local instance] riemannRochEffectiveIncrementScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensionalRiemannRochSubmodule
attribute [local instance] finiteDimensionalRiemannRochSubmodule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochDimension E ≤
      riemannRochDimension D +
        (Divisor.degree (residueDegree (k := k) (F := F)) (E - D)).toNat := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hbound := riemannRochDimension_add_nonnegative_le
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D (E - D) hnonnegative
  have heq : D + (E - D) = E := by
    ext P
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    omega
  rw [heq] at hbound
  exact hbound
end QEC.Coding.AlgebraicGeometry.GlobalPlace
