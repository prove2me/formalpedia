-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalClearedRepresentative_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:34:05.554761+00:00
-- url     : https://prove2.me/submissions/7ff56107-6bca-43a0-ab26-31064974e929

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_restriction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (k : ℕ) :
    let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
    (lpsOriginalFilledMeromorphicRestriction N hN G.val G.property).val =
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)^k *
      (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  let J : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalFilledJ N, lpsOriginalFilledChartMeromorphic_j N hN⟩
  let Fnorm : LPSOriginalFilledMeromorphicFunctionRing N hN :=
    ⟨lpsOriginalNormalizedFilledFunction N hN F,
      lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF⟩
  let e := lpsOriginalFilledFunctionToRestrictedMeromorphic N hN
  have hp : e G = e J^k * e Fnorm := by
    change e (J^k * Fnorm) = _
    rw [map_mul, map_pow]
  have he := congrArg Subtype.val hp
  change (lpsOriginalFilledMeromorphicRestriction N hN G.val G.property).val =
    ((lpsOriginalFilledMeromorphicRestriction N hN J.val J.property).val)^k *
      (lpsOriginalFilledMeromorphicRestriction N hN Fnorm.val Fnorm.property).val at he
  rw [lpsOriginalFilledMeromorphicRestriction_j,
    lpsOriginalNormalizedFilledFunction_restriction] at he
  exact he
end QEC.Coding.TannerLiftedProduct
