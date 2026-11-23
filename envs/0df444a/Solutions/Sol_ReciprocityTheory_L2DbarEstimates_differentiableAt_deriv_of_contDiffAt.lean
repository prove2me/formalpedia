-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.differentiableAt_deriv_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:30.349896+00:00
-- url     : https://prove2.me/submissions/c8a73000-e3b1-46c6-9ebf-625746f3ca84

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
theorem _root_.solution {k : ℝ → ℝ} {t : ℝ} (hk : ContDiffAt ℝ 2 k t) :
    DifferentiableAt ℝ (deriv k) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ k) t :=
    (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show DifferentiableAt ℝ (fun s => fderiv ℝ k s 1) t
  exact hd.clm_apply (differentiableAt_const _)
end ReciprocityTheory.L2DbarEstimates
