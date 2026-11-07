-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:21.922192+00:00
-- url     : https://prove2.me/submissions/31a008cf-b0c4-464e-a5e9-8e54b68355b8

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (y : ℝ) (hy : 0<y) (x : ℝ) :
    Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ)=
      (Real.exp (-2*Real.pi*y):ℂ)*fourier (1:ℤ) (x:AddCircle (1:ℝ)) := by
  have hz : (lpsHorocyclePoint y hy x:ℂ)=(x:ℂ)+Complex.I*(y:ℂ) := by
    apply Complex.ext <;> simp [lpsHorocyclePoint]
  rw [Function.Periodic.qParam,hz,fourier_coe_apply]
  norm_num only [Complex.ofReal_one,Int.cast_one,mul_one,div_one]
  rw [mul_add,Complex.exp_add]
  have hi : 2*(Real.pi:ℂ)*Complex.I*(Complex.I*(y:ℂ))=
      Complex.ofReal (-2*Real.pi*y) := by
    calc
      _ = Complex.I^2*(2*(Real.pi:ℂ)*(y:ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq];push_cast;ring
  rw [hi,←Complex.ofReal_exp,mul_comm]
end QEC.Coding.TannerLiftedProduct
