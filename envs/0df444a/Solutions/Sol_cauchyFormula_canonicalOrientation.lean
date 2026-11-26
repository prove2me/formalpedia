-- Prove2me | solution 1 for cauchyFormula_canonicalOrientation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:34.469057+00:00
-- url     : https://prove2.me/submissions/826ef4b8-1eef-4ca4-9f40-4af7a344fa9f

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology
theorem _root_.solution
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    f z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.canonicalOrientation.boundaryParam := by
  rw [contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
    Omega hf hz]
  field_simp [Real.pi_ne_zero, I_ne_zero]
