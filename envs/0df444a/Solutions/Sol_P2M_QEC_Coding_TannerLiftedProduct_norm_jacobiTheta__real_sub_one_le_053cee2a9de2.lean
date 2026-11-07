-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_norm_jacobiTheta__real_sub_one_le_053cee2a9de2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:45:12.485204+00:00
-- url     : https://prove2.me/submissions/837748a3-4cb1-4732-8feb-151a256a54cc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_jacobiTheta__term_norm_real_left_01b00fc6396f
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_hasSum_nat_jacobiTheta__real_cc862f55b35d
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
theorem _root_.solution (a : ℝ) (z : ℂ) (hz : 0<z.im) :
    ‖jacobiTheta₂ (a:ℂ) z-1‖ ≤ 2/(1-Real.exp (-Real.pi*z.im))*Real.exp (-Real.pi*z.im) := by
  let y := Real.exp (-Real.pi*z.im)
  have hy : y<1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hz)
  have hTerm : ∀ n : ℕ, ‖jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z‖ ≤ 2*y^(n+1) := by
    intro n
    have hp := norm_exp_mul_sq_le hz (n+1)
    have hn := norm_exp_mul_sq_le hz (-(n+1))
    rw [← jacobiTheta₂_term_norm_real_left _ a] at hp hn
    have hh := (norm_add_le _ _).trans (add_le_add hp hn)
    have hAbs : ((n:ℤ)+1).natAbs=n+1 := by
      rw [← Int.natCast_one,← Int.natCast_add,Int.natAbs_natCast]
    simpa only [Int.natAbs_neg,hAbs,two_mul] using hh
  have hSum : HasSum (fun n : ℕ => 2*y^(n+1)) (2*(y/(1-y))) := by
    have hG := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hy).mul_left (2*y)
    simpa only [pow_succ',div_eq_mul_inv,mul_assoc] using hG
  have hNorm : Summable (fun n : ℕ => ‖jacobiTheta₂_term (n+1) (a:ℂ) z +
      jacobiTheta₂_term (-(n+1)) (a:ℂ) z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hTerm hSum.summable
  rw [← (hasSum_nat_jacobiTheta₂_real a z hz).tsum_eq]
  have h := (norm_tsum_le_tsum_norm hNorm).trans
    ((hNorm.tsum_mono hSum.summable hTerm).trans_eq hSum.tsum_eq)
  convert! h using 1
  ring
end QEC.Coding.TannerLiftedProduct
