-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompatibleAffine_existsUnique_globalSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:01:10.470219+00:00
-- url     : https://prove2.me/submissions/f7dd7513-ea2a-4a80-92d6-6b744e0f11c7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroLaurentAffineCoefficientSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityLaurentAffineCoefficientSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalChartImage_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalLaurentImage_intersection
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_affineDifferentialChartPair_existsUnique_global
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_infinity_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_zero_affine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedOverlap_agreement


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
local notation "f0" => lpsOriginalComplexNormalGluedChartMap N hpos false
local notation "f1" => lpsOriginalComplexNormalGluedChartMap N hpos true
local notation "q0" => CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hpos)
local notation "q1" => CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hpos)
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
  LPSOriginalAffineKaehlerCompatibilityDictionary028
  LPSOriginalAffineKaehlerCompatibilityDictionary029
  LPSOriginalAffineKaehlerCompatibilityDictionary030
  LPSOriginalAffineKaehlerCompatibilityDictionary031
  LPSOriginalAffineKaehlerCompatibilityDictionary032
  LPSOriginalAffineKaehlerCompatibilityDictionary033
  LPSOriginalAffineKaehlerCompatibilityDictionary038
  LPSOriginalAffineKaehlerCompatibilityDictionary039
  LPSOriginalAffineKaehlerCompatibilityDictionary040
  LPSOriginalAffineKaehlerCompatibilityDictionary042
  LPSOriginalAffineKaehlerCompatibilityDictionary043
  LPSOriginalAffineKaehlerCompatibilityDictionary044
  LPSOriginalAffineKaehlerCompatibilityDictionary045
  LPSOriginalAffineKaehlerCompatibilityDictionary047
  LPSOriginalAffineKaehlerCompatibilityDictionary048
  LPSOriginalAffineKaehlerCompatibilityDictionary049
  LPSOriginalAffineKaehlerCompatibilityDictionary051
  LPSOriginalAffineKaehlerCompatibilityDictionary052
  LPSOriginalAffineKaehlerCompatibilityDictionary053
  LPSOriginalAffineKaehlerCompatibilityDictionary054
attribute [local instance] originalZeroLaurentRestrictionOpen originalInfinityLaurentRestrictionOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalZeroOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalInfinityOpen
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalNativeGlobalLaurentCompositeOpen
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor (f0)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor (f1)) ⊤
local notation "W" => Functor.obj (Scheme.Hom.opensFunctor (Spec.map (q0) ≫ (f0))) ⊤
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I)
    (hcompat : KaehlerDifferential.map ℂ ℂ R T a = KaehlerDifferential.map ℂ ℂ I T b) :
    ∃! z : Γ(Omega, ⊤),
      (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z =
        (lpsOriginalZeroImageFromKaehler N hpos).hom a ∧
      (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z =
        (lpsOriginalInfinityImageFromKaehler N hpos).hom b :=
  @affineDifferentialChartPair_existsUnique_global ℂ
    (CommRingCat.of R) (CommRingCat.of I) (CommRingCat.of T)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (q0) (q1)
    (fun _ => rfl) (fun _ => rfl)
    (lpsOriginalZeroLaurentAffineCoefficientSquare N hpos)
    (lpsOriginalInfinityLaurentAffineCoefficientSquare N hpos)
    X (f0) (f1) (originalZeroLaurentRestrictionOpen N hpos)
    (originalInfinityLaurentRestrictionOpen N hpos)
    (originalNativeGlobalZeroOpen N hpos) (originalNativeGlobalInfinityOpen N hpos) c
    (lpsOriginalComplexNormalGlobalConstantMap_zero_affine N hpos)
    (lpsOriginalComplexNormalGlobalConstantMap_infinity_affine N hpos)
    (lpsOriginalComplexNormalGluedOverlap_agreement N hpos)
    (lpsOriginalNativeGlobalChartImage_cover N hpos)
    (lpsOriginalNativeGlobalLaurentImage_intersection N hpos) a b hcompat
end QEC.Coding.TannerLiftedProduct
