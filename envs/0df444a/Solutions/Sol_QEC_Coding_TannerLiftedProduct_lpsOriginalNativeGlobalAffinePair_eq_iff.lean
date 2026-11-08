-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNativeGlobalAffinePair_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:41:47.186703+00:00
-- url     : https://prove2.me/submissions/0c980956-14b8-4da9-83a1-d08171cbcb9a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModuleGlobalIsoPair_eq_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "T" => lpsOriginalComplexNormalLaurentChart N hpos
local notation "Omega" => lpsOriginalComplexNormalDifferentialSheaf N hpos
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
attribute [local instance] originalNativeGlobalZeroOpen originalNativeGlobalInfinityOpen
local notation "U" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos false)) ⊤
local notation "V" => Functor.obj (Scheme.Hom.opensFunctor
  (lpsOriginalComplexNormalGluedChartMap N hpos true)) ⊤
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (z : Γ(Omega, ⊤))
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I) :
    lpsOriginalNativeGlobalAffinePair N hpos z = (a, b) ↔
    (Omega).presheaf.map (homOfLE le_top : U ⟶ ⊤).op z =
      (lpsOriginalZeroImageFromKaehler N hpos).hom a ∧
    (Omega).presheaf.map (homOfLE le_top : V ⟶ ⊤).op z =
      (lpsOriginalInfinityImageFromKaehler N hpos).hom b :=
  schemeModuleGlobalIsoPair_eq_iff Omega U V
    (lpsOriginalZeroImageFromKaehler N hpos).symm
    (lpsOriginalInfinityImageFromKaehler N hpos).symm z a b
end QEC.Coding.TannerLiftedProduct
