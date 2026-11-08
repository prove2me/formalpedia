-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldJ_interior_order_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:08:02.769245+00:00
-- url     : https://prove2.me/submissions/6c530eeb-bb5c-43b4-927a-baf30b77a82c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldToLocal_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary003
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) (algebraMap P K Polynomial.X) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  rw [lpsOriginalFieldLocalOrder_value,lpsOriginalFieldToLocal_j]
  change 0 ≤ meromorphicOrderAt
    (lpsOriginalFilledJ N ∘ (lpsOriginalLocalChart N hN (Sum.inl x)).symm)
    (lpsOriginalLocalChartCenter N hN (Sum.inl x))
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let e := lpsOriginalFilledInteriorChart N hN x
  have hs := lpsOriginalFilledInteriorChart_mem N hN x
  have ha := lpsOriginalFilledJ_interior_analytic N hN x (e (Sum.inl x)) (e.map_source hs)
  exact ha.meromorphicAt.meromorphicOrderAt_nonneg_iff.mpr
    ⟨lpsOriginalFilledJ N ∘ e.symm,ha,Filter.EventuallyEq.rfl⟩
end QEC.Coding.TannerLiftedProduct
