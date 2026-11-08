-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityKaehler_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:17:31.503225+00:00
-- url     : https://prove2.me/submissions/933861ef-e917-41d1-99fc-9d40ab17564d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalization_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_finiteType


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary027
  LPSOriginalLocalKaehlerFinitenessDictionary029
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
  LPSOriginalLocalKaehlerFinitenessDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_41
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_42
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_43
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_44
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_45
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_46
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_47
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_48
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_49
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_54
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_56
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_58
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_62
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_64
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_66
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : Module.Finite P (KaehlerDifferential ℂ R) := by
  let : Module.Finite P R := lpsOriginalInfinityNormalization_finite N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact Module.Finite.trans R (KaehlerDifferential ℂ R)
end QEC.Coding.TannerLiftedProduct
