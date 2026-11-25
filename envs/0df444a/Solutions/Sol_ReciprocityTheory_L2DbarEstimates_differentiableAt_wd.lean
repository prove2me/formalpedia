-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.differentiableAt_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:49.297944+00:00
-- url     : https://prove2.me/submissions/96f75361-745d-4cc7-a9c1-6646a999be49

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {j : Fin n} {f : V n → ℂ} {x : V n} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (wd n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) -
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.sub h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]
end ReciprocityTheory.L2DbarEstimates
