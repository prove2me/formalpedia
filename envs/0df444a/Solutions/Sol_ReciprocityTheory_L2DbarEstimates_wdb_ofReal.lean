-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wdb_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:55.729186+00:00
-- url     : https://prove2.me/submissions/10f96f11-165e-403c-b6cf-d6dbc248befc

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
theorem _root_.solution {j : Fin n} {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    wdb n j (fun y => (v y : ℂ)) x = conj (wd n j (fun y => (v y : ℂ)) x) := by
  simp only [wdb, wd, fderiv_ofReal_apply hv]
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  all_goals ring
end ReciprocityTheory.L2DbarEstimates
