-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.iter_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:24.305073+00:00
-- url     : https://prove2.me/submissions/b2e59aea-fd77-45da-b30d-4e019c9f564f

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
theorem _root_.solution (hf : IsShear F f) {z : A} (hz : z ∈ F 0) :
    ∀ i, iter f i z ∈ F 0 ∧ z - f (iter f i z) ∈ F i := by
  intro i
  induction i with
  | zero =>
    show (0 : A) ∈ F 0 ∧ z - f 0 ∈ F 0
    exact ⟨(F 0).zero_mem, (F 0).sub_mem hz (hf.1 _ (F 0).zero_mem)⟩
  | succ i ih =>
    obtain ⟨hw, hr⟩ := ih
    have hfw : f (iter f i z) ∈ F 0 := hf.1 _ hw
    have hr0 : z - f (iter f i z) ∈ F 0 := (F 0).sub_mem hz hfw
    have hw' : iter f (i + 1) z ∈ F 0 := (F 0).add_mem hw hr0
    refine ⟨hw', ?_⟩
    have hd : iter f (i + 1) z - iter f i z ∈ F i := by
      show iter f i z + (z - f (iter f i z)) - iter f i z ∈ F i
      simpa using hr
    have h2 := hf.2 i (iter f (i + 1) z) hw' (iter f i z) hw hd
    have h3 : z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f (i + 1) z - iter f i z)) := by
      show z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f i z + (z - f (iter f i z)) - iter f i z))
      abel
    rw [h3]
    exact (F (i + 1)).neg_mem h2
end IsShear
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
