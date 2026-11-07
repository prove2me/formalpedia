-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_qParam_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:16.090989+00:00
-- url     : https://prove2.me/submissions/fcba26c7-fb2f-4d74-b91c-b3ba3b5c79af

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
    ‖Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ)‖=Real.exp (-2*Real.pi*y) := by
  rw [Function.Periodic.norm_qParam]
  simp
end QEC.Coding.TannerLiftedProduct
