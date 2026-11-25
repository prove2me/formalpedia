-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.analyticSubset_chart_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:27.988373+00:00
-- url     : https://prove2.me/submissions/930fb170-c06c-4c5c-b5bc-e88c0cdcd64b

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal

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
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {S : Set X} (hS : A.IsAnalyticSubset S) (hint : interior S = ∅) (j : Fin A.n)
    {z : Fin e → ℂ} (hz : z ∈ (A.chart j) '' (S ∩ (A.chart j).source)) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ (A.chart j) '' (S ∩ (A.chart j).source) ∩ W, f w = 0 := by
  obtain ⟨x, ⟨-, hxs⟩, rfl⟩ := hz
  obtain ⟨W₀, hW₀, hxW₀, r, f, hf, hSW⟩ := hS x
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀) :=
    (A.chart j).isOpen_inter_preimage_symm hW₀
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W₀ := by
    refine ⟨(A.chart j).map_source hxs, ?_⟩
    show (A.chart j).symm ((A.chart j) x) ∈ W₀
    rw [(A.chart j).left_inv hxs]
    exact hxW₀
  obtain ⟨ε, hε0, hε⟩ := Metric.isOpen_iff.mp hopen _ hmem

  have hex : ∃ i, ∃ w ∈ Metric.ball ((A.chart j) x) ε, f i ((A.chart j).symm w) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (A.chart j).symm '' Metric.ball ((A.chart j) x) ε ⊆ S := by
      rintro _ ⟨w, hw, rfl⟩
      have hw' := hε hw
      have hin : (A.chart j).symm w ∈ S ∩ W₀ := by
        rw [hSW]
        exact ⟨hw'.2, fun i => hcon i w hw⟩
      exact hin.1
    have hop : IsOpen ((A.chart j).symm '' Metric.ball ((A.chart j) x) ε) :=
      (A.chart j).symm.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun w hw => (hε hw).1)
    have hint' : (A.chart j).symm ((A.chart j) x) ∈ interior S :=
      interior_maximal hsub hop ⟨_, Metric.mem_ball_self hε0, rfl⟩
    rw [hint] at hint'
    exact hint'
  obtain ⟨i, w₀, hw₀, hfw₀⟩ := hex
  refine ⟨Metric.ball ((A.chart j) x) ε, Metric.isOpen_ball, Metric.mem_ball_self hε0,
    (convex_ball _ _).isPreconnected, f i ∘ (A.chart j).symm, ?_, ⟨w₀, hw₀, hfw₀⟩, ?_⟩
  · exact (hf i j).mono hε
  · rintro w ⟨⟨y, ⟨hyS, hys⟩, rfl⟩, hw⟩
    have hw' := hε hw
    have hin : (A.chart j).symm ((A.chart j) y) ∈ S ∩ W₀ :=
      ⟨by rw [(A.chart j).left_inv hys]; exact hyS, hw'.2⟩
    rw [hSW] at hin
    exact hin.2 i
end ReciprocityTheory.AnForm.M
