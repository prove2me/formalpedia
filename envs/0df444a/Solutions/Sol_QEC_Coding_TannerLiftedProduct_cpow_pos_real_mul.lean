-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.cpow_pos_real_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:21.988303+00:00
-- url     : https://prove2.me/submissions/5288ca71-a0e7-41ec-ab89-3de9a9c1faf1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (r : ℝ) (hr : 0 < r) (z s : ℂ) (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ s = (r : ℂ) ^ s * z ^ s := by
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hn hz),
    Complex.cpow_def_of_ne_zero hn,Complex.cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul hr hz,add_mul,Complex.exp_add,Complex.ofReal_log hr.le]
end QEC.Coding.TannerLiftedProduct
