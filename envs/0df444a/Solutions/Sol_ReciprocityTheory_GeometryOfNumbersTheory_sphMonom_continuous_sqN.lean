-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_continuous_sqN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:05.534225+00:00
-- url     : https://prove2.me/submissions/656b80a2-c434-48d4-a338-ae3f715d95ef

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution : Continuous (fun z : Fin N → ℂ => sqN z) := by
  unfold sqN
  exact continuous_finset_sum _ fun i _ => (continuous_norm.comp (continuous_apply i)).pow 2
end ReciprocityTheory.GeometryOfNumbersTheory
