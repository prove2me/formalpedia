-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:22:20.345161+00:00
-- url     : https://prove2.me/submissions/31537fb4-9e84-461e-bdf1-d528f9f74b35

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicDecidableEq
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    rationalAdicResidueEquiv p
        (AdjoinRoot.mk (rationalAdicPolynomial p) b) =
      (rationalAdic p).residue (rationalAdicPolynomialToValuationRing p b) := by
  unfold rationalAdicResidueEquiv
  change (IsLocalRing.ResidueField.mapEquiv (rationalAdicLocalizationEquiv p))
      ((rationalAdicQuotientResidueEquiv p)
        ((Ideal.quotEquivOfEq (rationalAdic_asIdeal_eq_span p).symm)
          (AdjoinRoot.mk (rationalAdicPolynomial p) b))) = _
  unfold AdjoinRoot.mk
  change (IsLocalRing.ResidueField.mapEquiv (rationalAdicLocalizationEquiv p))
      ((rationalAdicQuotientResidueEquiv p)
        (Ideal.Quotient.mk p.asIdeal b)) = _
  unfold rationalAdicQuotientResidueEquiv
  rw [RingEquiv.ofBijective_apply,
    Ideal.algebraMap_quotient_residueField_mk]
  letI : IsLocalHom (rationalAdicLocalizationEquiv p).toRingHom :=
    ⟨fun _ hunit => by
      simpa using hunit.map (rationalAdicLocalizationEquiv p).symm.toRingHom⟩
  change IsLocalRing.ResidueField.map (rationalAdicLocalizationEquiv p).toRingHom
      ((IsLocalRing.residue (Localization.AtPrime p.asIdeal))
        (algebraMap k[X] (Localization.AtPrime p.asIdeal) b)) = _
  rw [IsLocalRing.ResidueField.map_residue,
    rationalAdicPolynomialToValuationRing]
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
