-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_ne_of_slope_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:51.211326+00:00
-- url     : https://prove2.me/submissions/d9a400c2-29b4-4efc-bc72-2fb335f0fbef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelRoot_neZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeriesAlgebraMap_injective


set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R : Type*) [CommRing R] [IsDomain R]
    (N : ℕ) (hN : 0 < N) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ζ η : R) (hη : η^N = 1) (hmn : m < n) :
    lpsOriginalPhaseCuspSeries R N m hm ζ ≠
      lpsOriginalPhaseCuspSeries R N n hn η := by
  intro he
  have hc := congrArg (fun j : lpsOriginalCuspSeriesRing R =>
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^n * j) he
  rw [lpsOriginalPhaseCuspSeries_clear R N m hm ζ n hmn.le,
    lpsOriginalPhaseCuspSeries_clear R N n hn η n (le_refl n),
    Nat.sub_self,pow_zero,one_mul] at hc
  have hs := lpsOriginalCuspSeriesAlgebraMap_injective R hc
  have hconst := congrArg PowerSeries.constantCoeff hs
  rw [map_mul,map_pow,PowerSeries.constantCoeff_X,
    zero_pow (Nat.sub_pos_of_lt hmn).ne',zero_mul,
    lpsOriginalPhaseCuspNumerator_constant] at hconst
  exact (pow_ne_zero (N-1) (lpsOriginalLevelRoot_neZero R N hN η hη)) hconst.symm
end QEC.Coding.TannerLiftedProduct
