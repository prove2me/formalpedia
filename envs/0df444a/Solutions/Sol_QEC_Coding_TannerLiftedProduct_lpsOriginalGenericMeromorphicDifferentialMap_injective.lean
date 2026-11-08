-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericMeromorphicDifferentialMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:54.381338+00:00
-- url     : https://prove2.me/submissions/7c567bd8-51bb-4175-ba51-b6bd615188cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericMeromorphicDifferentialMap_expand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJMeromorphicDerivative_ne_zero


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
theorem _root_.solution :
    Function.Injective (lpsOriginalGenericMeromorphicDifferentialMap N hpos) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro differentialForm h
  rw [lpsOriginalGenericMeromorphicDifferentialMap_expand] at h
  have hc := (mul_eq_zero.mp h).resolve_right lpsOriginalJMeromorphicDerivative_ne_zero
  have hz : lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm = 0 :=
    (lpsOriginalGenericToMeromorphicGerm N hpos).injective (hc.trans (map_zero _).symm)
  exact (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).injective
    (hz.trans (map_zero _).symm)
end QEC.Coding.TannerLiftedProduct
