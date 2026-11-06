-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.heightOne_valuationRing_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:17:45.656193+00:00
-- url     : https://prove2.me/submissions/b5127a13-4c47-4e18-a74c-5d4ecf70e2a8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralModelCentre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialPlaceTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_exists_heightOne_order_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
attribute [local instance] QEC.Coding.AlgebraicGeometry.placeTransportDVR
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution (P : GlobalPlace k K)
    (H : IsDedekindDomain.HeightOneSpectrum P.valuationRing) :
    (heightOnePlace (k := k) (K := K) H).order = P.order := by
  have hlt : P.valuation P.uniformizer < 1 := by
    rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  let t : P.valuationRing := ⟨P.uniformizer, hlt.le⟩
  have ht : t ≠ 0 := by
    intro hz
    have h := P.order_uniformizer
    have htzero : P.uniformizer = 0 := congrArg (fun x : P.valuationRing => (x : K)) hz
    rw [htzero] at h
    simp [GlobalPlace.order] at h
  obtain ⟨J, _, hJ⟩ := P.exists_heightOne_order_eq P.valuationRing
    (fun r => r.property) ⟨t, ht, hlt⟩
  have heq : H = J := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (IsLocalRing.eq_maximalIdeal H.isMaximal).trans
      (IsLocalRing.eq_maximalIdeal J.isMaximal).symm
  simpa only [heq] using hJ
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
