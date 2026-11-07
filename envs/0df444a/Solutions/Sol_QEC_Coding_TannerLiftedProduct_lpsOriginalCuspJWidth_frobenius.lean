-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspJWidth_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:39:35.515394+00:00
-- url     : https://prove2.me/submissions/963e44a7-3f82-482e-910c-24d745c6d154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSeriesFrobenius

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [CommRing R]
    (p : ℕ) [ExpChar R p] (hp : p≠0) (m : ℕ) (hm : m≠0) :
    (lpsOriginalCuspJWidth R m hm)^p=
      lpsOriginalCuspJWidth R (m*p) (Nat.mul_ne_zero hm hp) := by
  have hf : (lpsOriginalCuspJNumerator R)^p=
      PowerSeries.expand p hp (lpsOriginalCuspJNumerator R) :=
    lpsOriginalIntegerSeriesFrobenius R p hp lpsOriginalJZSeries
  rw [lpsOriginalCuspJWidth,mul_pow,←map_pow,←map_pow,hf,
    ←PowerSeries.expand_mul]
  rw [lpsOriginalCuspJWidth,←pow_mul]
end QEC.Coding.TannerLiftedProduct
