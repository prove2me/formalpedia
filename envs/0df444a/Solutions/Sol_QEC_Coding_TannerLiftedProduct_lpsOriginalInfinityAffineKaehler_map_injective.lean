-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityAffineKaehler_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:40:49.492405+00:00
-- url     : https://prove2.me/submissions/2fe9f986-4a7d-4c7b-a864-a51f21a48716

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehler_kernel_clear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_submodule_mem_of_forall_maximal_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChart_allMaximalPoints


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary025
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary026
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary040
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (KaehlerDifferential.map ℂ ℂ R K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro tau htau
  apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ R) ⊥ tau
  intro M hM
  obtain ⟨x,hx⟩ := lpsOriginalInfinityNormalChart_allMaximalPoints N hpos hN M
  obtain ⟨s,hs,hs0⟩ := lpsOriginalInfinityAffineKaehler_kernel_clear N hpos hN
    x.val x.property tau htau
  exact ⟨s,by rwa [hx],hs0⟩
end QEC.Coding.TannerLiftedProduct
