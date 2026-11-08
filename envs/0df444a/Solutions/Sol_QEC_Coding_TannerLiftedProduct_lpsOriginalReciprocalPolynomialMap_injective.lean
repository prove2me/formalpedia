-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomialMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:07:38.148319+00:00
-- url     : https://prove2.me/submissions/e47f8bde-d6ea-4402-8e77-4d86d866920d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPoleClearingAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
omit [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) := by
  let : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
  let : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
  exact (algebraMap J K).injective.comp (IsFractionRing.injective P J)
end QEC.Coding.TannerLiftedProduct
