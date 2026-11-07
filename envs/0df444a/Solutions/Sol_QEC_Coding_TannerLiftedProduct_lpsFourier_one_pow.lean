-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsFourier_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:22.847751+00:00
-- url     : https://prove2.me/submissions/26c03c09-a128-4618-97dc-d03fdf1e6ded

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) (x : ℝ) :
    (fourier (1:ℤ) (x:AddCircle (1:ℝ)))^n=fourier (n:ℤ) (x:AddCircle (1:ℝ)) := by
  rw [fourier_coe_apply,fourier_coe_apply,←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
