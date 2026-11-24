-- Prove2me | solution 1 for ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:30.946795+00:00
-- url     : https://prove2.me/submissions/97c938da-fcd9-4961-821e-6b45ec6fea82

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Theorems.Thm_ReciprocityTheory_AnForm_volume_zero_set_of_analyticOnNhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Metric Filter Topology
open MeasureTheory Metric Filter Topology
namespace ReciprocityTheory.AnForm
theorem _root_.solution {D : ℕ} (S : Set (Fin D → ℂ))
    (h : ∀ z ∈ S, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ S ∩ W, f w = 0) :
    volume S = 0 := by
  apply measure_null_of_locally_null
  intro z hz
  obtain ⟨W, hWo, hzW, hWc, f, hf, hne, hS⟩ := h z hz
  refine ⟨S ∩ W, inter_mem_nhdsWithin S (hWo.mem_nhds hzW), ?_⟩
  refine measure_mono_null (fun w hw => ?_) (volume_zero_set_of_analyticOnNhd hWo hWc hf hne)
  exact ⟨hw.2, hS w hw⟩
end ReciprocityTheory.AnForm
