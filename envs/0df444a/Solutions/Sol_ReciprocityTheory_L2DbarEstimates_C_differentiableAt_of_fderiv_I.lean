-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.differentiableAt_of_fderiv_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:05:04.477501+00:00
-- url     : https://prove2.me/submissions/ab61d395-cea3-4743-81f0-645bf06881b5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {n : ℕ} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v, fderiv ℝ f x (I • v) = I * fderiv ℝ f x v) : DifferentiableAt ℂ f x := by
  have hsmul : ∀ (c : ℂ) (v : V n), fderiv ℝ f x (c • v) = c * fderiv ℝ f x v := by
    intro c v
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [map_add, map_smul, map_smul, h, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let g' : V n →L[ℂ] ℂ :=
    ⟨⟨⟨fderiv ℝ f x, (fderiv ℝ f x).map_add⟩, fun c v => by simpa using hsmul c v⟩,
      (fderiv ℝ f x).continuous⟩
  exact (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨g', ContinuousLinearMap.ext fun _ => rfl⟩
end ReciprocityTheory.L2DbarEstimates.C
