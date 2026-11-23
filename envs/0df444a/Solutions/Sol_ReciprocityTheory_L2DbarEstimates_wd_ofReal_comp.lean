-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_ofReal_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:26.372328+00:00
-- url     : https://prove2.me/submissions/2abebd2f-e435-4cda-9122-b6f0ffd0e7ff

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply

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
theorem _root_.solution {j : Fin n} {k : ℝ → ℝ} {v : V n → ℝ} {x : V n}
    (hk : DifferentiableAt ℝ k (v x)) (hv : DifferentiableAt ℝ v x) :
    wd n j (fun y => (k (v y) : ℂ)) x = ((deriv k (v x) : ℝ) : ℂ) * wd n j (fun y => (v y : ℂ)) x := by
  have hkv : DifferentiableAt ℝ (fun y => k (v y)) x := hk.comp x hv
  have e : ∀ w, fderiv ℝ (fun y => (k (v y) : ℂ)) x w =
      ((deriv k (v x) : ℝ) : ℂ) * (fderiv ℝ v x w : ℂ) := by
    intro w
    rw [fderiv_ofReal_apply hkv, (show HasFDerivAt (fun y => k (v y)) _ x from
      hk.hasDerivAt.comp_hasFDerivAt x hv.hasFDerivAt).fderiv]
    simp
  simp only [wd, e, fderiv_ofReal_apply hv]
  ring
end ReciprocityTheory.L2DbarEstimates
