-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_reciprocal_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:46:28.646429+00:00
-- url     : https://prove2.me/submissions/e69b0b30-d98b-4f3d-b6c4-998bbc18f76d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalPolynomial_field_embedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4Ratio_reciprocal_field_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4MonicEquation_monic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary004
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (f : K)
    (hratio : (lpsOriginalGeneratedFunctionField N hpos).val f =
      (algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) :
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem f := by
  let ψ : K →+* H := (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  apply RingHom.IsIntegralElem.of_map (g := ψ)
    (show Function.Injective ψ from Subtype.val_injective)
  rw [lpsOriginalReciprocalPolynomial_field_embedding]
  refine ⟨lpsOriginalReciprocalE4MonicEquation N k A,
    lpsOriginalReciprocalE4MonicEquation_monic N k A, ?_⟩
  rw [show ψ f = _ from hratio]
  exact lpsOriginalE4Ratio_reciprocal_field_root N k A
end QEC.Coding.TannerLiftedProduct
