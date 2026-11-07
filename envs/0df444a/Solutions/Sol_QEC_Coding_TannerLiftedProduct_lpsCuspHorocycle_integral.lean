-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:42.813267+00:00
-- url     : https://prove2.me/submissions/6ddebeb0-0945-45da-b276-f6f4f65f5b26

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_coe
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    (∫ x : AddCircle (1:ℝ), ‖lpsCuspHorocycleCircle N f y x‖^2 ∂AddCircle.haarAddCircle)=
      ∫ x in (0:ℝ)..1, ‖f (lpsHorocyclePoint y hy x)‖^2 := by
  rw [AddCircle.integral_haarAddCircle]
  norm_num only [inv_one,one_smul]
  rw [←AddCircle.intervalIntegral_preimage 1 0]
  simp only [zero_add,lpsCuspHorocycleCircle_coe N f y hy]
end QEC.Coding.TannerLiftedProduct
