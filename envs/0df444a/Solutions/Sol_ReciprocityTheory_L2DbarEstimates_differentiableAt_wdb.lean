-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.differentiableAt_wdb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:25.698236+00:00
-- url     : https://prove2.me/submissions/f1f57eff-e33c-488a-8f3f-7d896fad81ec

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
    DifferentiableAt ℝ (wdb n j f) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun y => (fderiv ℝ f y (bas n j) +
    Complex.I * fderiv ℝ f y (Complex.I • bas n j)) / 2) x
  have h1 := hd.clm_apply (differentiableAt_const (bas n j))
  have h2 := (hd.clm_apply (differentiableAt_const (Complex.I • bas n j))).const_mul Complex.I
  refine ((h1.add h2).mul_const (2 : ℂ)⁻¹).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]
end ReciprocityTheory.L2DbarEstimates
