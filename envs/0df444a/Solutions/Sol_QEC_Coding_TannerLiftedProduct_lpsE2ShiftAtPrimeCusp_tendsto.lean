-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2ShiftAtPrimeCusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:07:12.791429+00:00
-- url     : https://prove2.me/submissions/1d542b2d-a9dc-4926-b1a1-3a1f14df14be

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2ShiftAtPrimeCusp_tendsto_of_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (r : Fin q) :
    Tendsto ((fun z : ℍ => EisensteinSeries.E2 (((r.val:ℝ)/(q:ℝ)) +ᵥ z))
      ∣[(2:ℤ)] lpsE2PrimeCuspMatrix q) UpperHalfPlane.atImInfty
        (𝓝 (if r.val+1=q then (q:ℂ)^2 else 1)) := by
  by_cases hr : r.val+1=q
  · let δ := lpsE2PrimeCuspMatrix 1
    have ha : (δ 0 0:ℝ)*(q:ℝ)=((r.val:ℤ):ℝ)+1 := by
      have h : (q:ℝ)=(r.val:ℝ)+1 := by exact_mod_cast hr.symm
      simpa [δ,lpsE2PrimeCuspMatrix,Matrix.of_apply] using h
    have hc : (δ 1 0:ℝ)*(q:ℝ)=(q:ℝ) := by
      simp [δ,lpsE2PrimeCuspMatrix,Matrix.of_apply]
    have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
    simpa only [if_pos hr,Int.cast_natCast,Complex.ofReal_natCast] using
      lpsE2ShiftAtPrimeCusp_tendsto_of_column q (r.val:ℤ) (q:ℝ) hq δ ha hc
  · have hlt : r.val+1<q := by omega
    have hd : ¬q∣r.val+1 := fun h => (Nat.le_of_dvd (by omega) h).not_gt hlt
    have hcop : Nat.Coprime (r.val+1) q :=
      ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hd).symm
    let δ := lpsE2PrimitiveColumn (r.val+1) q hcop
    have ha : (δ 0 0:ℝ)*(1:ℝ)=((r.val:ℤ):ℝ)+1 := by
      change ((r.val+1:ℕ):ℝ)*1=(r.val:ℝ)+1
      push_cast
      ring
    have hc : (δ 1 0:ℝ)*(1:ℝ)=(q:ℝ) := by
      change (q:ℝ)*1=(q:ℝ)
      ring
    simpa only [if_neg hr,Int.cast_natCast,Complex.ofReal_one,one_pow] using
      lpsE2ShiftAtPrimeCusp_tendsto_of_column q (r.val:ℤ) 1 (by norm_num) δ ha hc
end QEC.Coding.TannerLiftedProduct
