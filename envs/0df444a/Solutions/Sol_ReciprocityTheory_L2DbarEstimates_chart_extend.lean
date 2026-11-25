-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.chart_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:22.385798+00:00
-- url     : https://prove2.me/submissions/17cc242c-1553-4fc8-93e3-16a952ce5845

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (h : M → ℂ) (hh : Ck n z 1 h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ e.source) :
    ∃ H : V n → ℂ, ContDiff ℝ 1 H ∧ HasCompactSupport H ∧
      (∀ y ∈ e.target, H =ᶠ[𝓝 y] h ∘ e.symm) ∧ (∀ y ∉ e.target, H =ᶠ[𝓝 y] fun _ => 0) := by
  have hKc : IsCompact (e '' tsupport h) := hc.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  have hKt : e '' tsupport h ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  have hout : ∀ w, w ∉ e '' tsupport h → e.target.indicator (h ∘ e.symm) w = 0 := by
    intro w hw
    by_cases hwt : w ∈ e.target
    · rw [Set.indicator_of_mem hwt, Function.comp_apply]
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hw ⟨e.symm w, hmem, e.right_inv hwt⟩
    · exact Set.indicator_of_notMem hwt _
  have hin : ∀ y ∈ e.target, e.target.indicator (h ∘ e.symm) =ᶠ[𝓝 y] h ∘ e.symm := fun y hy =>
    Filter.eventually_of_mem (e.open_target.mem_nhds hy) fun w hw => Set.indicator_of_mem hw _
  have hzero : ∀ y ∉ e '' tsupport h, e.target.indicator (h ∘ e.symm) =ᶠ[𝓝 y] fun _ => 0 :=
    fun y hy => Filter.eventually_of_mem (hKc.isClosed.isOpen_compl.mem_nhds hy) fun w hw => hout w hw
  refine ⟨e.target.indicator (h ∘ e.symm), ?_, HasCompactSupport.intro hKc hout, hin,
    fun y hy => hzero y fun hyK => hy (hKt hyK)⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · exact ((hh e he).contDiffAt (e.open_target.mem_nhds hy)).congr_of_eventuallyEq (hin y hy)
  · exact contDiffAt_const.congr_of_eventuallyEq (hzero y fun hyK => hy (hKt hyK))
end ReciprocityTheory.L2DbarEstimates
