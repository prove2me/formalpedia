-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_coeff_norm_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:59.810744+00:00
-- url     : https://prove2.me/submissions/ca8f23c7-7814-4be0-93d5-5614adc97d04

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_qParam_norm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_hasSum
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*
      (Real.exp (-2*Real.pi*y))^n) := by
  have h := (lpsWeightTwoCuspHorocycle_hasSum N f y hy 0).summable.norm
  simpa only [norm_mul,norm_pow,lpsHorocyclePoint_qParam_norm] using h
end QEC.Coding.TannerLiftedProduct
