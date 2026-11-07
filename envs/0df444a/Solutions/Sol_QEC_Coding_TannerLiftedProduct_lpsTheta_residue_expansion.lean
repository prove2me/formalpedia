-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsTheta_residue_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:40.171365+00:00
-- url     : https://prove2.me/submissions/5b32c757-bc15-4be5-8e7c-ab397a911a7a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsShiftedTheta_eq_tsum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaResidue_term
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℤ) (c : ℕ) [NeZero c] (z : ℂ) (hz : 0<z.im) :
    jacobiTheta (z+2*(a:ℂ)/(c:ℂ)) =
      ∑ r : Fin c, lpsQuadraticPhase a c r *
        lpsShiftedTheta ((r.val:ℂ)/(c:ℂ)) ((c:ℂ)^2*z) := by
  let τ := z+2*(a:ℂ)/(c:ℂ)
  have ht : 0<τ.im := by simpa [τ] using hz
  have hs : Summable (fun n : ℤ => Complex.exp ((Real.pi:ℂ)*Complex.I*(n:ℂ)^2*τ)) := by
    simpa only [jacobiTheta₂_term,mul_zero,zero_add] using (hasSum_jacobiTheta₂_term 0 ht).summable
  let e : Fin c × ℤ ≃ ℤ := ((Int.divModEquiv c).trans (Equiv.prodComm ℤ (Fin c))).symm
  have hse := hs.comp_injective e.injective
  dsimp only [Function.comp_def,τ] at hse
  rw [jacobiTheta,← e.tsum_eq,hse.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lpsShiftedTheta_eq_tsum,← tsum_mul_left]
  apply tsum_congr
  intro k
  change Complex.exp ((Real.pi:ℂ)*Complex.I*((k*(c:ℤ)+(r.val:ℤ):ℤ):ℂ)^2*τ)=_
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
  exact lpsThetaResidue_term a k c r z
end QEC.Coding.TannerLiftedProduct
