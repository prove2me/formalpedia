-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericKaehlerCoefficientEquiv_D_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:22:37.407979+00:00
-- url     : https://prove2.me/submissions/07fd3a4e-0985-4abb-bc87-594d40f190c4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_31
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_39
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_41
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_42
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6f8db27f7a_43
variable [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalGenericKaehlerCoefficientEquiv N hpos
      (KaehlerDifferential.D ℂ K (algebraMap P K Polynomial.X)) = 1 := by
  rw [lpsOriginalGenericKaehlerCoefficientEquiv_D_polynomial,
    Polynomial.derivative_X, map_one]
end QEC.Coding.TannerLiftedProduct
