-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_mellin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:55.421346+00:00
-- url     : https://prove2.me/submissions/1efc6309-0c1a-4c5b-8526-45d05bc99e5c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareLSeries_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_div_rpow_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleSquareMean_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsCuspHorocycleSquareMean N f y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s := by
  have hp (n : ℕ) : (lpsWeightTwoCusp_squareCoeff N f n:ℂ)=0 ∨
      0<4*Real.pi*(n:ℝ) := by
    by_cases hn : n=0
    · left
      subst n
      rw [lpsWeightTwoCusp_squareCoeff_zero,Complex.ofReal_zero]
    · right
      have hn' : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      positivity
  have hsum : Summable (fun n : ℕ => ‖(lpsWeightTwoCusp_squareCoeff N f n:ℂ)‖/
      (4*Real.pi*(n:ℝ))^s.re) := by
    have h := (lpsWeightTwoCusp_squareCoeff_div_rpow_summable N f s hs).div_const
      ((4*Real.pi)^s.re)
    apply h.congr
    intro n
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg n),div_mul_eq_div_div,div_right_comm,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (lpsWeightTwoCusp_squareCoeff_nonneg N f n)]
  have h := hasSum_mellin hp (by linarith : 0<s.re)
    (fun y hy => lpsCuspHorocycleSquareMean_hasSum N f y hy) hsum
  have he (n : ℕ) :
      Complex.Gamma s*(lpsWeightTwoCusp_squareCoeff N f n:ℂ)/((4*Real.pi*(n:ℝ):ℝ):ℂ)^s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries.term (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s n := by
    by_cases hn : n=0
    · subst n
      simp [lpsWeightTwoCusp_squareCoeff_zero]
    · rw [LSeries.term_of_ne_zero hn]
      rw [Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity : 0≤4*Real.pi) (Nat.cast_nonneg n)]
      norm_cast
      ring
  simp_rw [he] at h
  exact h.unique ((lpsWeightTwoCusp_squareLSeries_summable N f s hs).hasSum.mul_left _)
end QEC.Coding.TannerLiftedProduct
