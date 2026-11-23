-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:27:47.086959+00:00
-- url     : https://prove2.me/submissions/89cbc296-35e7-4e79-9726-3fe691a38a39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x y : EuclideanSpace ℂ ι) :
    (Hf x y).im = inner ℝ y ((-I : ℂ) • x) := by
  simp only [Hf, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | rw [Complex.inner]
    | rw [real_inner_eq_re_inner ℂ]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, RCLike.re_to_complex,
    RCLike.inner_apply]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
