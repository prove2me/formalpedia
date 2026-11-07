-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycle_weight_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:42:00.820447+00:00
-- url     : https://prove2.me/submissions/461190fb-fcb5-4f6d-a940-42e63dc4b790

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (y : ℝ) (n : ℕ) :
    (Real.exp (-2*Real.pi*y))^(2*n)=Real.exp (-4*Real.pi*(n:ℝ)*y) := by
  rw [←Real.exp_nat_mul]
  congr 1
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct
