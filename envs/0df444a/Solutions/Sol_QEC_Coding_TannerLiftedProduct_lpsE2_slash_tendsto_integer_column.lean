-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_slash_tendsto_integer_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:08:08.052613+00:00
-- url     : https://prove2.me/submissions/37bf93a5-82fb-4af7-bdb5-81bea6225bc2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_slash_tendsto_of_column
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
theorem _root_.solution (M : GL (Fin 2) ℝ)
    (hd : 0<M.det.val) (a c : ℤ) (t : ℝ) (ht : t≠0)
    (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t)
    (hpos : 0<Int.gcd a c) :
    Tendsto (EisensteinSeries.E2 ∣[(2:ℤ)] M) UpperHalfPlane.atImInfty
      (𝓝 ((((Int.gcd a c:ℕ):ℂ)/(t:ℂ))^2/(M.det.val:ℂ))) := by
  obtain ⟨a',c',hcop,ha',hc'⟩ := Int.exists_gcd_one hpos
  let δ := lpsE2IntegerPrimitiveColumn a' c' hcop
  let g : ℝ := (Int.gcd a c:ℝ)/t
  have hg : g≠0 := div_ne_zero (by exact_mod_cast hpos.ne') ht
  have hA : (δ 0 0:ℝ)*g=M 0 0 := by
    rw [ha]
    change (a':ℝ)*((Int.gcd a c:ℝ)/t)=(a:ℝ)/t
    have he : (a:ℝ)=(a':ℝ)*(Int.gcd a c:ℝ) := by exact_mod_cast ha'
    rw [he]
    ring
  have hC : (δ 1 0:ℝ)*g=M 1 0 := by
    rw [hc]
    change (c':ℝ)*((Int.gcd a c:ℝ)/t)=(c:ℝ)/t
    have he : (c:ℝ)=(c':ℝ)*(Int.gcd a c:ℝ) := by exact_mod_cast hc'
    rw [he]
    ring
  simpa only [g,Complex.ofReal_div,Complex.ofReal_natCast] using
    lpsE2_slash_tendsto_of_column M hd δ g hg hA hC
end QEC.Coding.TannerLiftedProduct
