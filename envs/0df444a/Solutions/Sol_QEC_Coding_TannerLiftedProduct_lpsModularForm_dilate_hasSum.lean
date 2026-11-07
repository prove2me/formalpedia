-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:14:58.939522+00:00
-- url     : https://prove2.me/submissions/703821a3-b9c9-4055-aa79-c3d651b633b6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_qParam
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
theorem _root_.solution (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => lpsModularDilationCoefficient
      (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) m n *
        Function.Periodic.qParam 1 (z:ℂ)^n) (lpsModularForm_dilate N m hm f z) := by
  let a : ℕ→ℂ := fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)
  let g : ℕ→ℂ := fun n => lpsModularDilationCoefficient a m n *
    Function.Periodic.qParam 1 (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hm hxy
  have ho : ∀ n, n∉Set.range (fun k : ℕ => m*k) → g n=0 := by
    intro n hn
    have hnd : ¬m∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [g,lpsModularDilationCoefficient,hnd]
  have hp : (1:ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hs := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) hp
    (lpsE2AffineMatrix m hm 0 • z)
  rw [lpsE2AffineMatrix_qParam] at hs
  have hcomp : HasSum (g ∘ (fun n : ℕ => m*n))
      (f (lpsE2AffineMatrix m hm 0 • z)) := by
    apply hs.congr_fun
    intro n
    have hd : m∣m*n := dvd_mul_right _ _
    have hdiv : m*n/m=n := Nat.mul_div_cancel_left n hm
    simp only [Function.comp_def,g,lpsModularDilationCoefficient,if_pos hd,hdiv,pow_mul,a]
  exact (hi.hasSum_iff ho).mp hcomp
end QEC.Coding.TannerLiftedProduct
