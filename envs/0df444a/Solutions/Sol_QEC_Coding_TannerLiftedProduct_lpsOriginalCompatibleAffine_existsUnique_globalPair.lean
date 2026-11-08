-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompatibleAffine_existsUnique_globalPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:04:10.803012+00:00
-- url     : https://prove2.me/submissions/ba139335-7b6b-4b1d-aff7-61c9c867e0d5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineChartDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerCompatibility
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompatibleAffine_existsUnique_globalSection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalAffinePair_eq_iff

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
theorem _root_.solution
    (a : KaehlerDifferential ℂ R) (b : KaehlerDifferential ℂ I)
    (hcompat : KaehlerDifferential.map ℂ ℂ R T a = KaehlerDifferential.map ℂ ℂ I T b) :
    ∃! z : Γ(Omega, ⊤), lpsOriginalNativeGlobalAffinePair N hpos z = (a, b) := by
  obtain ⟨z, hz, huniq⟩ := lpsOriginalCompatibleAffine_existsUnique_globalSection N hpos a b hcompat
  refine ⟨z, (lpsOriginalNativeGlobalAffinePair_eq_iff N hpos z a b).mpr hz, ?_⟩
  intro z' hz'
  exact huniq z' ((lpsOriginalNativeGlobalAffinePair_eq_iff N hpos z' a b).mp hz')
end QEC.Coding.TannerLiftedProduct
