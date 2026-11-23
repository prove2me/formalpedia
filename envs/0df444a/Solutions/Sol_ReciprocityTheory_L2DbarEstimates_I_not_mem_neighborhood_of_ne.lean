-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.not_mem_neighborhood_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:07.030999+00:00
-- url     : https://prove2.me/submissions/2dea3f8b-82b5-4a17-b7b2-d2b24498e543

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (W : M → Set M) (m : ℝ) (hL : IsLocalData n g ph r W m)
    {p q x : M} (hp : p ∈ zeroSet n g) (hq : q ∈ zeroSet n g) (hpq : q ≠ p) (hx : x ∈ W p) :
    x ∉ W q := fun hxq =>
  Set.disjoint_left.1 ((hL.2 p hp).2.2.2.2 q hq hpq) (subset_closure hx) (subset_closure hxq)
end ReciprocityTheory.L2DbarEstimates.I
