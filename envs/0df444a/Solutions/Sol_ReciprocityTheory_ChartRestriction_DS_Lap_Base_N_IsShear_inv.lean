-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.IsShear.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:52.764582+00:00
-- url     : https://prove2.me/submissions/114eb780-9952-4bc5-86b8-3cfa0207dee6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_iter_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_IsShear_right_inv

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
theorem _root_.solution (hF : IsFil F L) (hf : IsShear F f) : IsShear F (iter f L) := by
  refine ⟨fun z hz => (IsShear.iter_mem hf hz L).1, ?_⟩
  intro j x hx y hy hxy
  have hu0 : iter f L x ∈ F 0 := (IsShear.iter_mem hf hx L).1
  have hv0 : iter f L y ∈ F 0 := (IsShear.iter_mem hf hy L).1
  have hfu : f (iter f L x) = x := IsShear.right_inv hF hf hx
  have hfv : f (iter f L y) = y := IsShear.right_inv hF hf hy
  have key : ∀ k, k ≤ j → iter f L x - iter f L y ∈ F k := by
    intro k
    induction k with
    | zero => intro _; exact (F 0).sub_mem hu0 hv0
    | succ k ih =>
      intro hk
      have h1 := hf.2 k _ hu0 _ hv0 (ih (by omega))
      rw [hfu, hfv] at h1
      have h2 : x - y ∈ F (k + 1) := hF.anti (k + 1) j hk hxy
      have h3 : iter f L x - iter f L y = (x - y) - (x - y - (iter f L x - iter f L y)) := by abel
      rw [h3]
      exact (F (k + 1)).sub_mem h2 h1
  have h1 := hf.2 j _ hu0 _ hv0 (key j le_rfl)
  rw [hfu, hfv] at h1
  have h3 : iter f L x - iter f L y - (x - y) = -(x - y - (iter f L x - iter f L y)) := by abel
  rw [h3]
  exact (F (j + 1)).neg_mem h1
end IsShear
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
