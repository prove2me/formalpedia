-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.directFactorPlace_order_baseGenerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:31.445994+00:00
-- url     : https://prove2.me/submissions/512e8b39-623d-473a-9f26-666bd2f1144a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_order_of_integral_eq_multiplicity
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
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    GlobalPlace.order (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (R k) F (generator p.asIdeal)) =
      (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) : ℤ) := by
  let q : R k := generator p.asIdeal
  let x : B k F := algebraMap (R k) (B k F) q
  have hq : q ≠ 0 := by
    intro hzero
    apply p.ne_bot
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p.asIdeal).mpr hzero
  have hx : x ≠ 0 := by
    simpa only [x, q, map_zero] using
      (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F).ne hq
  have hpmap : Ideal.map (algebraMap (R k) (B k F)) p.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot p.ne_bot
  have hspan : Ideal.span ({x} : Set (B k F)) =
      Ideal.map (algebraMap (R k) (B k F)) p.asIdeal := by
    dsimp only [x, q]
    calc
      Ideal.span
          ({algebraMap (R k) (B k F) (generator p.asIdeal)} : Set (B k F)) =
          Ideal.map (algebraMap (R k) (B k F))
            (Ideal.span ({generator p.asIdeal} : Set (R k))) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap (R k) (B k F)) p.asIdeal := by
        rw [Ideal.span_singleton_generator p.asIdeal]
  rw [IsScalarTower.algebraMap_apply (R k) (B k F) F]
  change GlobalPlace.order
      (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (B k F) F x) = _
  rw [AffinePlace.globalPlace_order_of_integral_eq_multiplicity k F
    (directFactorPlace k F p P) hx, directFactorPlace_asIdeal, hspan]
  exact_mod_cast
    (Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hpmap
      (Ideal.Factors.isPrime p.asIdeal P)).symm
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
