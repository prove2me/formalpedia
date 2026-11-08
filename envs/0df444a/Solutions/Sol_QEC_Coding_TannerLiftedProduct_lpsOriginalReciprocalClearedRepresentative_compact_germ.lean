-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalClearedRepresentative_compact_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:39:45.569485+00:00
-- url     : https://prove2.me/submissions/e40bc5e5-79bd-4951-ae4f-761e02b8a0c1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_compact_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalCriterionDictionary004
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) (k : ℕ) :
    lpsOriginalCompactMeromorphicGermAlgHom N hN
      (lpsOriginalReciprocalClearedRepresentative N hN F.val F.property k) =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
        ((algebraMap P K Polynomial.X)^k*f) := by
  change lpsOriginalCompactMeromorphicGermAlgHom N hN
    ((⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ :
      LPSOriginalFilledMeromorphicFunctionRing N hN)^k *
      ⟨lpsOriginalNormalizedFilledFunction N hN F.val,
        lpsOriginalNormalizedFilledFunction_meromorphic N hN F.val F.property⟩) = _
  rw [map_mul, map_pow,
    lpsOriginalNormalizedFilledFunction_compact_germ N hN F.val F.property, hF,
    ←lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j N hpos hN]
  rw [map_mul, map_pow]
end QEC.Coding.TannerLiftedProduct
