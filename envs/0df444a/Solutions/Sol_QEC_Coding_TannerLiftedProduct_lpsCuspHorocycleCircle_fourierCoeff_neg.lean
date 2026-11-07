-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_fourierCoeff_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:32.008991+00:00
-- url     : https://prove2.me/submissions/54030c89-e1e3-4f0d-b1a0-a41e03e257c0

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleTerm_fourierCoeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_fourierCoeff_hasSum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (k : ℤ) (hk : k<0) :
    fourierCoeff (lpsCuspHorocycleCircle N f y) k=0 := by
  have h := lpsCuspHorocycleCircle_fourierCoeff_hasSum N f y hy k
  have hn (n:ℕ) : (n:ℤ)≠k := by omega
  simp_rw [lpsCuspHorocycleTerm_fourierCoeff,if_neg (hn _)] at h
  exact h.unique hasSum_zero
end QEC.Coding.TannerLiftedProduct
