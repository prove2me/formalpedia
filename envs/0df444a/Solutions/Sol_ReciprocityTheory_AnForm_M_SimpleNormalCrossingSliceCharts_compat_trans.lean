-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:20.688074+00:00
-- url     : https://prove2.me/submissions/7481acd4-9e8c-4386-844f-3b04b11b5219

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
variable {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
theorem _root_.solution {e : ℕ} (A : FinHolAtlas e X) {ψ₁ ψ₂ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (h₁ : IsCompatChart A ψ₁) (h₂ : IsCompatChart A ψ₂) {v : Fin e → ℂ} (hv : v ∈ ψ₁.target)
    (hv2 : ψ₁.symm v ∈ ψ₂.source) : AnalyticAt ℂ (ψ₂ ∘ ψ₁.symm) v := by
  obtain ⟨j, hj⟩ := A.cover (ψ₁.symm v)
  have ha : AnalyticAt ℂ (A.chart j ∘ ψ₁.symm) v := (h₁ j).2 v ⟨hv, hj⟩
  have hb : AnalyticAt ℂ (ψ₂ ∘ (A.chart j).symm) ((A.chart j ∘ ψ₁.symm) v) := by
    apply (h₂ j).1
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ₁.symm v)) ∈ ψ₂.source
    rw [(A.chart j).left_inv hj]
    exact hv2
  have hc := hb.comp ha
  apply hc.congr
  have hn : ψ₁.symm ⁻¹' (A.chart j).source ∈ 𝓝 v :=
    (ψ₁.continuousAt_symm hv).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hn] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
