-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleLocalLeadingCoefficient_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:41:29.664329+00:00
-- url     : https://prove2.me/submissions/54e4b12b-3769-409c-a740-53a6d13bdfe3

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
namespace GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
private theorem globalAdele_exp_neg_mul_lt_one_iff_le (x : ℤᵐ⁰) (n : ℤ) :
    WithZero.exp (-n) * x < 1 ↔ x ≤ WithZero.exp (n - 1) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← WithZero.log_lt_log (mul_ne_zero WithZero.exp_ne_zero hx) one_ne_zero]
  rw [WithZero.log_mul WithZero.exp_ne_zero hx, WithZero.log_exp,
    WithZero.log_one]
  rw [← WithZero.log_le_iff_le_exp hx]
  omega
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

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
    LinearMap.ker (globalAdeleLocalLeadingCoefficient D P) =
      Submodule.comap
        (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)).subtype
        (globalAdeleFilter (k := k) (F := F) D) := by
  letI : Algebra k P.residueField := residueAlgebra P
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  change P.residue (globalAdeleLocalLeadingCoefficientValue D P a) = 0 ↔
    ∀ Q, Q.valuation ((a.val : GlobalAdele (k := k) (F := F)).val Q) ≤
      WithZero.exp (D Q)
  rw [P.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change P.valuation
      (Differential.localParameterPower P (D P + 1) *
        ((a.val : GlobalAdele (k := k) (F := F)).val P)) < 1 ↔ _
  rw [map_mul, globalAdele_localParameterPower_valuation,
    globalAdele_exp_neg_mul_lt_one_iff_le]
  constructor
  · intro hP Q
    by_cases hQP : Q = P
    · subst Q
      simpa only [add_sub_cancel_right] using hP
    · have haQ := a.property Q
      simpa only [Finsupp.add_apply, placeDivisor_apply_of_ne P Q (Ne.symm hQP),
        add_zero] using haQ
  · intro ha
    simpa using ha P
end QEC.Coding.AlgebraicGeometry.GlobalPlace
