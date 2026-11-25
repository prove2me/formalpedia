-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_isClosed_of_isAnalyticSubset__ea2fe8163d5c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:36.357665+00:00
-- url     : https://prove2.me/submissions/e2a1994c-804c-439a-bf49-80259c17a0f0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Pullback
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open FinHolAtlas Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)
end ReciprocityTheory.AnForm.M
