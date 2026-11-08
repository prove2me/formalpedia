-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalTransportedInverseCoefficientRange_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:21:46.055766+00:00
-- url     : https://prove2.me/submissions/8454d2f4-2bb3-48a5-ba6b-bc9441117f42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInverseDifferentialLattice
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityKaehler_finite

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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_106
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_107
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_110
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_114
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_116
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_118
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_120
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_122
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_124
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalTransportedInverseOmegaKModule
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_129
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_131
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_133
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_136
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_402e0474f5_138
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Module.Finite P (lpsOriginalTransportedInverseCoefficientMap N hpos).range := by
  let : Module.Finite P (KaehlerDifferential ℂ R) := lpsOriginalInfinityKaehler_finite N hpos
  exact Module.Finite.range _
end QEC.Coding.TannerLiftedProduct
