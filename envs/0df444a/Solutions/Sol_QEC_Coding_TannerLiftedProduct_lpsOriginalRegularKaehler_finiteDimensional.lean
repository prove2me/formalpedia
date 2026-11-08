-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRegularKaehler_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:41.730205+00:00
-- url     : https://prove2.me/submissions/ddc4bab0-b316-4028-93c1-b9c17e20332c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularCoefficientSubmodule_finiteDimensional

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018
  LPSOriginalLocalKaehlerFinitenessDictionary031
  LPSOriginalLocalKaehlerFinitenessDictionary032
  LPSOriginalLocalKaehlerFinitenessDictionary033
  LPSOriginalLocalKaehlerFinitenessDictionary034
  LPSOriginalLocalKaehlerFinitenessDictionary035
  LPSOriginalLocalKaehlerFinitenessDictionary036
  LPSOriginalLocalKaehlerFinitenessDictionary037
  LPSOriginalLocalKaehlerFinitenessDictionary038
  LPSOriginalLocalKaehlerFinitenessDictionary039
  LPSOriginalLocalKaehlerFinitenessDictionary040
  LPSOriginalLocalKaehlerFinitenessDictionary041
  LPSOriginalLocalKaehlerFinitenessDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_61
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_63
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_65
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_67
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_71
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_73
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_d13105efee_75
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) := by
  let : FiniteDimensional ℂ (lpsOriginalRegularCoefficientMap N hpos).range :=
    lpsOriginalRegularCoefficientSubmodule_finiteDimensional N hpos
  apply FiniteDimensional.of_injective (lpsOriginalRegularCoefficientMap N hpos).rangeRestrict
  intro x y h
  apply Subtype.ext
  apply (lpsOriginalGenericKaehlerCoefficientEquiv N hpos).injective
  exact congrArg Subtype.val h
end QEC.Coding.TannerLiftedProduct
