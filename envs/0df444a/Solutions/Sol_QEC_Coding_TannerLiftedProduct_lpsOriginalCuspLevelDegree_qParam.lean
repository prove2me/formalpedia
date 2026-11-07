-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspLevelDegree_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:47:00.803447+00:00
-- url     : https://prove2.me/submissions/62db20db-aa6c-4d0f-b329-1573911eb952

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_mul_width
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspLevelDegree_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ : SL(2, ℤ)) (z : ℂ) :
    Function.Periodic.qParam (lpsOriginalCuspGroup M ρ).strictWidthInfty z ^
      lpsOriginalCuspLevelDegree N M ρ =
        Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty z := by
  change (Complex.exp ((2 : ℂ) * Real.pi * I * z /
    ((lpsOriginalCuspGroup M ρ).strictWidthInfty : ℂ))) ^ lpsOriginalCuspLevelDegree N M ρ =
      Complex.exp ((2 : ℂ) * Real.pi * I * z / ((lpsOriginalCuspGroup N ρ).strictWidthInfty : ℂ))
  rw [←Complex.exp_nat_mul]
  congr 1
  have hmR : (lpsOriginalCuspGroup M ρ).strictWidthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty * (lpsOriginalCuspLevelDegree N M ρ : ℝ) := by
    rw [lpsOriginalCuspWidthNat_cast, lpsOriginalCuspWidthNat_cast]
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (lpsOriginalCuspLevelDegree_mul_width N M hNM ρ).symm
    rw [Nat.cast_mul] at h
    exact h
  have hmC := congrArg Complex.ofReal hmR
  rw [Complex.ofReal_mul, Complex.ofReal_natCast] at hmC
  rw [hmC, div_mul_eq_div_div]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lpsOriginalCuspLevelDegree_positive N M hNM ρ)))
end QEC.Coding.TannerLiftedProduct
