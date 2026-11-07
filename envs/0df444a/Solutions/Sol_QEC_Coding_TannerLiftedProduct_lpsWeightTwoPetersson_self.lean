-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:46.666725+00:00
-- url     : https://prove2.me/submissions/90acde66-5deb-40b0-8dcc-32ec2c381d65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (f : ℍ → ℂ) (τ : ℍ) :
    petersson 2 f f τ = ((‖f τ‖^2*τ.im^2:ℝ):ℂ) := by
  rw [petersson, ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp
end QEC.Coding.TannerLiftedProduct
