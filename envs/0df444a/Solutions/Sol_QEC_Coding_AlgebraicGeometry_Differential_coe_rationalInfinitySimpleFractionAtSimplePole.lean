-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalInfinitySimpleFractionAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:03.863617+00:00
-- url     : https://prove2.me/submissions/c1386ff7-4112-42b8-afb4-7c745126cbab

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
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


section
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
private theorem coe_rationalInfinitySimpleFractionCoefficient
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionCoefficient q b hq hb :
      (GlobalPlace.rationalInfinity k).valuationRing) : RatFunc k) =
      -(RatFunc.X *
        (algebraMap k[X] (RatFunc k) b /
          algebraMap k[X] (RatFunc k) q)) :=
  rfl
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (q b : k[X]) (hq : q.Monic) (hb : b.degree < q.degree) :
    ((rationalInfinitySimpleFractionAtSimplePole q b hq hb :
      simplePoleDifferentialLattice (GlobalPlace.rationalInfinity k)) :
        Differential k (RatFunc k)) =
        (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) q) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  have hDX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  change
    ((rationalInfinitySimpleFractionCoefficient q b hq hb :
      (GlobalPlace.rationalInfinity k).valuationRing) : RatFunc k) •
      logarithmicDifferential (k := k) (F := RatFunc k)
        (RatFunc.X : RatFunc k)⁻¹ = _
  rw [coe_rationalInfinitySimpleFractionCoefficient,
    logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    Derivation.leibniz_inv, hDX]
  simp only [smul_smul, smul_eq_mul]
  field_simp [RatFunc.X_ne_zero, RatFunc.algebraMap_ne_zero hq.ne_zero]
end QEC.Coding.AlgebraicGeometry.Differential
