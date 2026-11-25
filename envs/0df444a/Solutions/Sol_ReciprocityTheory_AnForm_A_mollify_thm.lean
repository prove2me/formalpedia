-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mollify_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:22.547411+00:00
-- url     : https://prove2.me/submissions/b5c5e009-80c5-46b2-bbba-d6058837dace

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMaxLogConvex_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : MollifyStatement := by
  intro D ρ U φ hU hφ
  refine ⟨fun ε hε => mollify_main ρ hU hφ hε, fun z hz => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hR0 : 0 < r / 2 := by positivity
  have hRU : closedBall z (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hlim := (polyMaxLogConvex_thm D U φ z (r / 2) hU hφ hR0 hRU).2.2.2
  have hsh : ∀ ε, 0 < ε → ε < r / 2 → z ∈ shrink U ε := fun ε _ hεR =>
    (closedBall_subset_closedBall hεR.le).trans hRU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).1
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with ε hε hεR
    exact ((mollify_main ρ hU hφ hε).2.2.2 z (hsh ε hε hεR)).2
end ReciprocityTheory.AnForm.A
