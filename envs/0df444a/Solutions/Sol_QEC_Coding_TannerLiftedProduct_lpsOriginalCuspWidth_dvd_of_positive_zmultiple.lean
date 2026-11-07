-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidth_dvd_of_positive_zmultiple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:38.362507+00:00
-- url     : https://prove2.me/submissions/5c32bc7f-c471-4d59-a370-765852d11b8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (z : ℤ) (hz : z • (a : ℝ) = (b : ℝ)) : a ∣ b := by
  have haz : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbz : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [zsmul_eq_mul] at hz
    nlinarith
  have hzint : 0 < z := by exact_mod_cast hzpos
  have he : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_of_lt hzint)
  refine ⟨z.toNat, ?_⟩
  have hreal : (b : ℝ) = (a : ℝ) * (z.toNat : ℝ) := by
    rw [he, zsmul_eq_mul] at *
    nlinarith
  exact_mod_cast hreal
end QEC.Coding.TannerLiftedProduct
