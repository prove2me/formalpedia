-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:38:58.0225+00:00
-- url     : https://prove2.me/submissions/92df42e4-e7e6-48d9-99d2-23c81043ba4d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehler_kernel_clear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_submodule_mem_of_forall_maximal_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_interior_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalChart_allMaximalPoints


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary016
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (KaehlerDifferential.map ℂ ℂ R K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro tau htau
  apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ R) ⊥ tau
  intro M hM
  obtain ⟨x,hx⟩ := lpsOriginalZeroNormalChart_allMaximalPoints N hpos hN M
  obtain ⟨s,hs,hs0⟩ := lpsOriginalZeroAffineKaehler_kernel_clear N hpos hN (Sum.inl x)
    (lpsOriginalFieldJ_interior_order_nonnegative N hpos hN x) tau htau
  exact ⟨s,by rwa [hx],hs0⟩
end QEC.Coding.TannerLiftedProduct
