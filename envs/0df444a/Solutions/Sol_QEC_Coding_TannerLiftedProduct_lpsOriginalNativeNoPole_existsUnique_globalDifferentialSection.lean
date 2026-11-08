-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNativeNoPole_existsUnique_globalDifferentialSection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:07:44.557482+00:00
-- url     : https://prove2.me/submissions/0627f06c-9007-4131-8b95-e3a4e1dc28bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeGlobalRegularity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompatibleAffine_existsUnique_globalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehler_map_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeGlobalAffinePair_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehler_map_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
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
attribute [local instance]
  LPSOriginalAffineKaehlerCompatibilityDictionary001
  LPSOriginalAffineKaehlerCompatibilityDictionary002
  LPSOriginalAffineKaehlerCompatibilityDictionary003
  LPSOriginalAffineKaehlerCompatibilityDictionary004
  LPSOriginalAffineKaehlerCompatibilityDictionary011
  LPSOriginalAffineKaehlerCompatibilityDictionary012
  LPSOriginalAffineKaehlerCompatibilityDictionary013
  LPSOriginalAffineKaehlerCompatibilityDictionary014
  LPSOriginalAffineKaehlerCompatibilityDictionary023
  LPSOriginalAffineKaehlerCompatibilityDictionary024
  LPSOriginalAffineKaehlerCompatibilityDictionary025
  LPSOriginalAffineKaehlerCompatibilityDictionary026
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (omega : KaehlerDifferential ℂ K)
    (h : ∀ x : LPSOriginalFilledCurve N, 0 ≤ meromorphicOrderValuation
      (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃! z : Γ(Omega, ⊤),
      KaehlerDifferential.map ℂ ℂ R K (lpsOriginalNativeGlobalAffinePair N hpos z).1 = omega ∧
      KaehlerDifferential.map ℂ ℂ I K (lpsOriginalNativeGlobalAffinePair N hpos z).2 = omega := by
  obtain ⟨p, hp, _⟩ := lpsOriginalNativeNoPole_existsUnique_compatibleAffineKaehlerPreimages
    N hpos hN omega h
  obtain ⟨z, hz, _⟩ := lpsOriginalCompatibleAffine_existsUnique_globalPair N hpos p.1 p.2 hp.2.2
  have h0 := (congrArg (fun t : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I =>
    KaehlerDifferential.map ℂ ℂ R K t.1) hz).trans hp.1
  have h1 := (congrArg (fun t : KaehlerDifferential ℂ R × KaehlerDifferential ℂ I =>
    KaehlerDifferential.map ℂ ℂ I K t.2) hz).trans hp.2.1
  refine ⟨z, ⟨h0, h1⟩, ?_⟩
  intro z' hz'
  apply lpsOriginalNativeGlobalAffinePair_injective N hpos
  apply Prod.ext
  · exact lpsOriginalZeroAffineKaehler_map_injective N hpos hN (hz'.1.trans h0.symm)
  · exact lpsOriginalInfinityAffineKaehler_map_injective N hpos hN (hz'.2.trans h1.symm)
end QEC.Coding.TannerLiftedProduct
