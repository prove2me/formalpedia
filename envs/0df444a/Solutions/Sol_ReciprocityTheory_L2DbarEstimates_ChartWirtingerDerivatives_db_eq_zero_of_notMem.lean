-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.db_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:50.774505+00:00
-- url     : https://prove2.me/submissions/3b7288bc-07ac-463e-a002-06a1eee3d30b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_db_of_not_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_chart_mem_target
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_chart_symm_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hx : x ∉ tsupport f) : db n z j f x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hxe⟩ := h
    rw [db_eq_wdb n z e he j f x hxe]
    have h0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have ht := (e.continuousAt_symm (chart_mem_target n z e he x hxe)).tendsto
    rw [chart_symm_apply n z e he x hxe] at ht
    have h1 : (f ∘ e.symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
      filter_upwards [h0.comp_tendsto ht] with w hw
      simpa using hw
    rw [wdb_congr n j _ _ _ h1]
    simp [wdb]
  · exact db_of_not_chart n z j f x h
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
