-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspParameter_cancelPowers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:46.814238+00:00
-- url     : https://prove2.me/submissions/cae3061d-9552-4572-9ea4-dd903226d350

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {R : Type*} [CommRing R]
    (m D i : ℕ) (hi : i≤D) :
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*D) *
      (IsLocalization.Away.invSelf (S:=lpsOriginalCuspSeriesRing R)
        (PowerSeries.X : PowerSeries R))^(m*i)=
      (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^(m*(D-i)) := by
  have he : m*D=m*(D-i)+m*i := by
    rw [←Nat.mul_add,Nat.sub_add_cancel hi]
  rw [he,pow_add,mul_assoc,←mul_pow,IsLocalization.Away.mul_invSelf,one_pow,mul_one]
end QEC.Coding.TannerLiftedProduct
