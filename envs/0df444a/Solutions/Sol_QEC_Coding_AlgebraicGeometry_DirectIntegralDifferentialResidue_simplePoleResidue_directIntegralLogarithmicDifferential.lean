-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.simplePoleResidue_directIntegralLogarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:43:25.007288+00:00
-- url     : https://prove2.me/submissions/e4751af9-c232-41d4-a08c-6e740bd7bee3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialResidue_directFactorPlace_order_baseGenerator
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] Ideal.Factors.quotientResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_49
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    Differential.simplePoleResidue (k := k) (F := F)
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (directIntegralLogarithmicDifferentialAtSimplePole k F p P b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
          (directIntegralToValuationRing k F p P b) *
        (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField) := by
  unfold directIntegralLogarithmicDifferentialAtSimplePole
  rw [Differential.simplePoleResidue_smul,
    Differential.simplePoleResidue_logarithmicDifferential,
    directFactorPlace_order_baseGenerator]
  simp only [Int.cast_natCast]
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
