-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_mem_rationalAdic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:41.419569+00:00
-- url     : https://prove2.me/submissions/6a2fda3e-b9a2-4302-aebd-048782ea0544

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialTraceRegularity_functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply



set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_scalarTower
attribute [local instance] integralDifferentialTraceRegularity_scalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_54
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_58
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_61
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) ∈
      Differential.localDifferentialLattice (GlobalPlace.rationalAdic p) := by
  rw [functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
    k F b t]
  simpa only [Differential.coe_rationalAdicPolynomialDifferential] using
    (Differential.rationalAdicPolynomialDifferential p
      (directIntegralDifferentialTracePolynomial k F b t)).property
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
