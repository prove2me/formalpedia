-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericToMeromorphicGerm_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:13.072587+00:00
-- url     : https://prove2.me/submissions/3b146f23-bf3b-4da0-aa26-fb65378920ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericJCoordinate_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic


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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalGenericToMeromorphicGerm N hpos (algebraMap P K Polynomial.X) =
      lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic := by
  change lpsOriginalHolomorphicFractionToMeromorphicGerm
    (algebraMap P K Polynomial.X).val = _
  rw [lpsOriginalGenericJCoordinate_value,
    lpsOriginalHolomorphicFractionToMeromorphicGerm_holomorphic]
end QEC.Coding.TannerLiftedProduct
