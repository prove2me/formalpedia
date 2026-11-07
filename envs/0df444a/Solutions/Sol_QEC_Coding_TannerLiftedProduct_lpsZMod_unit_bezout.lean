-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsZMod_unit_bezout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:41.508445+00:00
-- url     : https://prove2.me/submissions/14018509-2136-409a-b2f8-8cccc97d41bf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℤ) (ha : IsUnit (a:ZMod N)) :
    ∃ b u : ℤ, a*u-b*(N:ℤ)=1 := by
  obtain ⟨u,hu⟩ := ZMod.intCast_surjective (↑(ha.unit⁻¹):ZMod N)
  have had : (a:ZMod N)*(u:ZMod N)=1 := by
    have h : (ha.unit:ZMod N)*↑(ha.unit⁻¹)=1 := by simp
    simpa only [ha.unit_spec,← hu] using h
  have hz : ((a*u-1:ℤ):ZMod N)=0 := by
    push_cast
    rw [had]
    ring
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  refine ⟨b,u,?_⟩
  linear_combination hb
end QEC.Coding.TannerLiftedProduct
