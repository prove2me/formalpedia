-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_parseval_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:21.962476+00:00
-- url     : https://prove2.me/submissions/026ffba5-9163-42a2-b74f-6fe5393ade21

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_memLp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun k : ℤ => ‖fourierCoeff (lpsCuspHorocycleCircle N f y) k‖^2)
      (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle) := by
  have hm := lpsCuspHorocycleCircle_memLp N f y hy
  have h := hasSum_sq_fourierCoeff hm.toLp
  have he := fourierCoeff_congr_ae hm.coeFn_toLp
  simp_rw [he] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]
end QEC.Coding.TannerLiftedProduct
