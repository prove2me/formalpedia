-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericMeromorphicDifferentialMap_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:17.584017+00:00
-- url     : https://prove2.me/submissions/f233754f-d4b4-4972-b7c8-e45f0e1dee61

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericKaehler_expand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericMeromorphicDifferentialMap_D_j

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane TensorProduct
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_135
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_141
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_143
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_145
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_146
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_147
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_178
variable [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalGenericMeromorphicDifferentialMap N hpos differentialForm =
      lpsOriginalGenericToMeromorphicGerm N hpos
        (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) *
          lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
            (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) := by
  conv_lhs => rw [lpsOriginalGenericKaehler_expand N hpos differentialForm]
  rw [map_smul, lpsOriginalGenericMeromorphicDifferentialMap_D_j]
  rfl
end QEC.Coding.TannerLiftedProduct
