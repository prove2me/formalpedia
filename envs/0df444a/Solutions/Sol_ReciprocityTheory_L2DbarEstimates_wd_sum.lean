-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:47.68275+00:00
-- url     : https://prove2.me/submissions/60729538-8a4b-4242-8fdb-d3a7573bfdd7

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {j : Fin n} {f : ι → V n → ℂ} {x : V n}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    wd n j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, wd n j (f i) x := by
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y
    simp [Finset.sum_apply]
  unfold wd
  rw [e, (HasFDerivAt.sum fun i hi => (hf i hi).hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
end ReciprocityTheory.L2DbarEstimates
