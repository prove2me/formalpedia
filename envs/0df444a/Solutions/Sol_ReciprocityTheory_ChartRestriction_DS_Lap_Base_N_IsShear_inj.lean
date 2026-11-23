-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:41.566543+00:00
-- url     : https://prove2.me/submissions/ae54daa1-da67-4683-ad5a-67c25b8aa61a

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
theorem _root_.solution (hF : IsFil F L) (hf : IsShear F f) {x y : A} (hx : x ∈ F 0) (hy : y ∈ F 0)
    (h : f x = f y) : x = y := by
  have key : ∀ j, x - y ∈ F j := by
    intro j
    induction j with
    | zero => exact (F 0).sub_mem hx hy
    | succ j ih =>
      have h1 := hf.2 j x hx y hy ih
      rw [h, sub_self, zero_sub] at h1
      simpa using (F (j + 1)).neg_mem h1
  have h2 := key L
  rw [hF.bot, Submodule.mem_bot, sub_eq_zero] at h2
  exact h2
end IsShear
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
