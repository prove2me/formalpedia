-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:55.152587+00:00
-- url     : https://prove2.me/submissions/42816cd3-5796-42ea-9871-7e5a25eff07a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeQParam_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeFinite_hasSum_mask
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (p*n) (UpperHalfPlane.qExpansion 1 f)*
      Function.Periodic.qParam 1 (z:ℂ)^n)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  let g : ℕ→ℂ := fun n => if p∣n then
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      Function.Periodic.qParam (p:ℝ) (z:ℂ)^n else 0
  have hg : HasSum g ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) :=
    lpsHeckeFinite_hasSum_mask N p f z
  have hi : Function.Injective (fun n : ℕ => p*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hab
  have ho : ∀ n, n∉Set.range (fun k : ℕ => p*k) → g n=0 := by
    intro n hn
    have hnd : ¬p∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [g,hnd]
  have h := (hi.hasSum_iff ho).mpr hg
  apply h.congr_fun
  intro n
  dsimp only [Function.comp_def,g]
  rw [if_pos (dvd_mul_right p n),pow_mul,lpsHeckeQParam_pow]
end QEC.Coding.TannerLiftedProduct
