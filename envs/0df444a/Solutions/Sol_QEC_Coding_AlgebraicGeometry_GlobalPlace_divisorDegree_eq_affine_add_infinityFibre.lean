-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_eq_affine_add_infinityFibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:02:20.778234+00:00
-- url     : https://prove2.me/submissions/f7497a94-3d2e-4827-95d3-cef936622166

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finsupp_sum_eq_affine_add_infinityFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_affine
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_inverseFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] riemannRochPolarDegreeAlgebra
namespace GlobalPlace
@[simp]
private theorem weightedDivisor_apply
    {P : Type*} (weight : P → ℕ) (D : Divisor P) (P : P) :
    weightedDivisor weight D P = D P * (weight P : ℤ) :=
  rfl
private theorem weightedDivisor_sum
    {P : Type*} (weight : P → ℕ) (D : Divisor P) :
    (weightedDivisor weight D).sum (fun _ value => value) =
      Divisor.degree weight D := by
  classical
  unfold weightedDivisor Divisor.degree Divisor.degreeHom Finsupp.sum
  erw [Finsupp.support_onFinset]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hzero : D P * (weight P : ℤ) = 0 <;> simp [hzero] <;> rfl
private theorem affineFinsupp_weightedDivisor
    (D : Divisor (GlobalPlace k F)) :
    affineFinsupp (k := k) (F := F)
        (weightedDivisor (residueDegree (k := k) (F := F)) D) =
      weightedDivisor (AffinePlace.residueDegree k F)
        (affineFinsupp (k := k) (F := F) D) := by
  ext C
  simp only [affineFinsupp, Finsupp.comapDomain_apply,
    weightedDivisor_apply]
  rw [residueDegree_eq_affine (AffinePlace.globalPlace k F C) C rfl]
private theorem infinityFibreFinsupp_weightedDivisor
    (D : Divisor (GlobalPlace k F)) :
    infinityFibreFinsupp (k := k) (F := F)
        (weightedDivisor (residueDegree (k := k) (F := F)) D) =
      weightedDivisor
        (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (infinityFibreFinsupp (k := k) (F := F) D) := by
  ext C
  simp only [infinityFibreFinsupp, Finsupp.comapDomain_apply,
    weightedDivisor_apply]
  rw [residueDegree_eq_inverseFibre
    (InverseAffinePlace.infinityFibreGlobalPlace
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s)
      (κ := AffinePlace.constantAlgebra k F) C) C rfl]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarDegreeAlgebra
attribute [local instance] riemannRochPolarDegreeAlgebra
open QEC.Coding.AlgebraicGeometry.GlobalPlace
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) D =
      Divisor.degree (AffinePlace.residueDegree k F)
          (affineFinsupp (k := k) (F := F) D) +
        Divisor.degree
          (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
          (infinityFibreFinsupp (k := k) (F := F) D) := by
  let weighted := weightedDivisor (residueDegree (k := k) (F := F)) D
  have hsplit := finsupp_sum_eq_affine_add_infinityFibre
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s)
    (k := k) (F := F) weighted
  rw [affineFinsupp_weightedDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D,
    infinityFibreFinsupp_weightedDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D,
    weightedDivisor_sum, weightedDivisor_sum] at hsplit
  rw [weightedDivisor_sum] at hsplit
  exact hsplit
end QEC.Coding.AlgebraicGeometry.GlobalPlace
