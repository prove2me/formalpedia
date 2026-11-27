-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isClosed_of_isAnalyticSubset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:24:41.467895+00:00
-- url     : https://prove2.me/submissions/6e6cae17-03a5-4819-bf47-d88cba29f522

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree

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
theorem _root_.solution (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x (hx : x ∉ S)
  obtain ⟨W, hWo, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨j, hj⟩ := A.cover x
  have hxz : ¬ ∀ i, f i x = 0 := by
    intro hz
    have hmem : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hz⟩
    exact hx hmem.1
  push_neg at hxz
  obtain ⟨i, hi⟩ := hxz
  have hcont : ContinuousAt (f i) x := by
    have hxt : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]
      exact hxW
    have h1 : ContinuousAt (f i ∘ (A.chart j).symm) (A.chart j x) := (hf i j _ hxt).continuousAt
    have h3 := h1.comp ((A.chart j).continuousAt hj)
    refine h3.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hcont.eventually_ne hi, hWo.mem_nhds hxW] with y hy hyW
  intro hyS
  have hmem : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hmem
  exact hy (hmem.2 i)
end ReciprocityTheory.AnForm.M
