-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:06.308805+00:00
-- url     : https://prove2.me/submissions/ceb75042-f3ed-4a2a-bb63-4328c609cce9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace IsShear
theorem _root_.solution (hF : IsFil F L) (hf : IsShear F f) (hg : IsShear F g) : IsShear F (f ∘ g) := by
  refine ⟨fun x hx => hf.1 _ (hg.1 x hx), ?_⟩
  intro j x hx y hy hxy
  show f (g x) - f (g y) - (x - y) ∈ F (j + 1)
  have h1 := hg.2 j x hx y hy hxy
  have hgxy : g x - g y ∈ F j := by
    have h2 : g x - g y = (g x - g y - (x - y)) + (x - y) := by abel
    rw [h2]
    exact (F j).add_mem (hF.anti j (j + 1) (Nat.le_succ j) h1) hxy
  have h3 := hf.2 j (g x) (hg.1 x hx) (g y) (hg.1 y hy) hgxy
  have h4 : f (g x) - f (g y) - (x - y) = (f (g x) - f (g y) - (g x - g y)) + (g x - g y - (x - y)) := by abel
  rw [h4]
  exact (F (j + 1)).add_mem h3 h1
end IsShear
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
