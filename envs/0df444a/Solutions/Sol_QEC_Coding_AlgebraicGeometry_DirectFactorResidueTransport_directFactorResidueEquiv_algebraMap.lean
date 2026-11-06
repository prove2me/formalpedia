-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueEquiv_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:38:08.573733+00:00
-- url     : https://prove2.me/submissions/47f4d795-30db-430e-bead-af56edba8dc4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
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


section
namespace QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] directFactorResidueTransport_constantAlgebra
attribute [local instance] directFactorResidueTransport_isTorsionFree
open DirectIntegralDifferentialResidue
@[simp]
private theorem coe_directFactorLocalizationEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ((directFactorLocalizationEquiv k F p P
        (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b) :
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing) : F) =
      algebraMap (B k F) F b := by
  let C : AffinePlace.carrier k F := directFactorPlace k F p P
  change ((directFactorLocalizationEquiv k F p P
      (algebraMap (B k F) (Localization.AtPrime C.asIdeal) b) :
    (C.valuation F).valuationSubring) : F) = algebraMap (B k F) F b
  unfold directFactorLocalizationEquiv
  exact congrArg Subtype.val
    ((Localization.algEquiv C.asIdeal.primeCompl
      (C.valuationSubringAtPrime F)).commutes b)
end QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueTransport_constantAlgebra
attribute [local instance] directFactorResidueTransport_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport.directFactorResidueTransport_isTorsionFree
attribute [local instance] directFactorResidueTransport_isTorsionFree
open DirectIntegralDifferentialResidue
namespace QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    directFactorResidueEquiv k F p P
        (algebraMap (B k F) (P : Ideal (B k F)).ResidueField b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
        (directIntegralToValuationRing k F p P b) := by
  letI : (P : Ideal (B k F)).IsMaximal :=
    (Ideal.Factors.isPrime p.asIdeal P).isMaximal
      (Ideal.Factors.ne_bot p.asIdeal P)
  letI : IsLocalHom (directFactorLocalizationEquiv k F p P).toRingHom :=
    ⟨fun _ hunit => by
      simpa using hunit.map
        (directFactorLocalizationEquiv k F p P).symm.toRingHom⟩
  unfold directFactorResidueEquiv
  change IsLocalRing.ResidueField.map
      (directFactorLocalizationEquiv k F p P).toRingHom
        ((IsLocalRing.residue (Localization.AtPrime (P : Ideal (B k F))))
          (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  apply congrArg
    (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
  apply Subtype.ext
  change ((directFactorLocalizationEquiv k F p P
      (algebraMap (B k F) (Localization.AtPrime (P : Ideal (B k F))) b) :
    (AffinePlace.globalPlace k F
      (directFactorPlace k F p P)).valuationRing) : F) =
    algebraMap (B k F) F b
  exact coe_directFactorLocalizationEquiv k F p P b
end QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
