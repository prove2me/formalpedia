-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.698882+00:00
-- url     : https://prove2.me/submissions/11039a12-13fd-4614-9fea-e062827ac30f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have hf' : A.SmoothOn Set.univ f := hf
  have hc : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have h0 := (hf' j).continuousOn
    simpa using h0
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    hc.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]
end ReciprocityTheory.AnForm.M
