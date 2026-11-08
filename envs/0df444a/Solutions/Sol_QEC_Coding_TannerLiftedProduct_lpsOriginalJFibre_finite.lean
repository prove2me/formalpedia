-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJFibre_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:33:26.034062+00:00
-- url     : https://prove2.me/submissions/694ed256-0bf1-4a86-bd2a-fd9e07dd2e6e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFibre_inverse_not_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_finite_nonanalytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
include hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℂ) :
    {y : Q | lpsOriginalFilledJ N (Sum.inl y) = a}.Finite := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  have hF := lpsOriginalFilledChartMeromorphic_inv N hN
    (lpsOriginalFilledChartMeromorphic_add N hN (lpsOriginalFilledChartMeromorphic_j N hN)
      (lpsOriginalFilledChartMeromorphic_neg N hN (lpsOriginalFilledChartMeromorphic_const N hN a)))
  have hbad := lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN _ hF
  exact (Set.Finite.preimage Sum.inl_injective.injOn hbad).subset
    (fun y hy => lpsOriginalJFibre_inverse_not_analytic N hpos hN a y hy)
end QEC.Coding.TannerLiftedProduct
