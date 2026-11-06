-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleLocalLeadingCoefficient_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:38.240672+00:00
-- url     : https://prove2.me/submissions/ed9963f0-0dd7-4bc4-8f3c-981fd26168e8

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
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
open scoped Polynomial RatFunc WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    letI : Algebra k P.residueField := residueAlgebra P
    Function.Surjective (globalAdeleLocalLeadingCoefficient D P) := by
  letI : Algebra k P.residueField := residueAlgebra P
  classical
  let n : ℤ := D P + 1
  intro y
  obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective y
  let x : F := Differential.localParameterPower P (-n) * (z : F)
  let a₀ : GlobalAdele (k := k) (F := F) :=
    globalAdeleUpdate (k := k) (F := F) (zeroGlobalAdele (k := k) (F := F)) P x
  have ha₀ : a₀ ∈ globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) := by
    intro Q
    by_cases hQP : Q = P
    · subst Q
      have hzle : P.valuation (z : F) ≤ 1 :=
        (mem_valuationRing_iff P (z : F)).mp z.property
      have hvalue : (a₀ : GlobalAdele (k := k) (F := F)).val P = x := by
        simp only [a₀, globalAdeleUpdate, Function.update_self]
      rw [hvalue]
      simp only [x, map_mul, globalAdele_localParameterPower_valuation, neg_neg]
      have hzle' : P.valuation (z : F) ≤ WithZero.exp (0 : ℤ) := by
        simpa only [WithZero.exp_zero] using hzle
      calc
        WithZero.exp n * P.valuation (z : F) ≤
            WithZero.exp n * WithZero.exp 0 := mul_le_mul_right hzle' _
        _ = WithZero.exp (D P + 1) := by
          rw [← WithZero.exp_add]
          simp only [add_zero, n]
        _ = WithZero.exp ((D + placeDivisor P) P) := by
          simp only [Finsupp.add_apply, placeDivisor_apply]
    · have hzero : (a₀ : GlobalAdele (k := k) (F := F)).val Q = 0 := by
        simp only [a₀, globalAdeleUpdate, zeroGlobalAdele,
          Function.update_of_ne hQP, Pi.zero_apply]
      rw [hzero, map_zero]
      exact zero_le
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  have hpi_ne : Differential.localParameter P ≠ 0 :=
    Differential.localParameter_ne_zero (k := k) (F := F) P
  have hcancel :
      Differential.localParameterPower P n *
          (Differential.localParameterPower P (-n) * (z : F)) = (z : F) := by
    simp only [Differential.localParameterPower,
      Differential.localParameterUnit, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← mul_assoc, ← zpow_add₀ hpi_ne, add_neg_cancel, zpow_zero, one_mul]
  change P.residue (globalAdeleLocalLeadingCoefficientValue D P ⟨a₀, ha₀⟩) = y
  rw [← hz]
  congr 1
  apply Subtype.ext
  simp only [globalAdeleLocalLeadingCoefficientValue]
  change Differential.localParameterPower P (D P + 1) *
      ((a₀ : GlobalAdele (k := k) (F := F)).val P) = (z : F)
  rw [show (a₀ : GlobalAdele (k := k) (F := F)).val P = x by
    simp only [a₀, globalAdeleUpdate, Function.update_self]]
  simpa only [n, x] using hcancel
end QEC.Coding.AlgebraicGeometry.GlobalPlace
