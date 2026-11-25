-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mixedDisc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:21.824856+00:00
-- url     : https://prove2.me/submissions/4423b090-4980-4c2a-90a0-d591ede4b339

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] ReciprocityTheory.ChartRestriction.G.Geo.instRealIPS
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]
end ReciprocityTheory.ChartRestriction.G.Geo
