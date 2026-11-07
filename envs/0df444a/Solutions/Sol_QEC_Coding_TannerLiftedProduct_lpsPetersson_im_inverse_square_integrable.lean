-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPetersson_im_inverse_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:54.324583+00:00
-- url     : https://prove2.me/submissions/7144bf7e-c2bc-49a0-b42a-6adee0ff736f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℝ) (ha : 0<a) :
    IntegrableOn (fun y : ℝ => (1/y)^2) (Ioi a) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) ha
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  simp
end QEC.Coding.TannerLiftedProduct
