-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_sum_ind_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:00.679367+00:00
-- url     : https://prove2.me/submissions/9b907012-b501-4b2c-a75e-a47df8522a8b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (E : ℕ → Set X) (hd : Pairwise (Function.onFun Disjoint E)) (g : X → ℝ)
    (x : X) (N : ℕ) : ∑ m ∈ Finset.range N, |(E m).indicator g x| ≤ |g x| := by
  classical
  by_cases hx : ∃ m ∈ Finset.range N, x ∈ E m
  · obtain ⟨m0, hm0, hxm0⟩ := hx
    rw [Finset.sum_eq_single m0]
    · simp only [Set.indicator_of_mem hxm0, le_refl]
    · intro m _ hm
      have hxm : x ∉ E m := fun h' => Set.disjoint_left.mp (hd hm) h' hxm0
      simp [Set.indicator_apply, hxm]
    · intro h'
      exact absurd hm0 h'
  · push_neg at hx
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun m hm => ?_)) (abs_nonneg _)
    simp [Set.indicator_apply, hx m hm]
end ReciprocityTheory.AnForm.M
