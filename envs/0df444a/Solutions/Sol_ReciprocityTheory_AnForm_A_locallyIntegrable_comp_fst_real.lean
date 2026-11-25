-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.locallyIntegrable_comp_fst_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:18.096814+00:00
-- url     : https://prove2.me/submissions/0ed00b4a-e6c1-4f71-9cb2-8618d1494863

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun p : ℝ × ℝ => g p.1) volume := by
  intro x
  refine ⟨Metric.closedBall x.1 1 ×ˢ Metric.closedBall x.2 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos), ?_⟩
  rw [← integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall),
    Measure.volume_eq_prod]
  have h1 := (integrable_indicator_iff measurableSet_closedBall).mpr
    (hg.integrableOn_isCompact (isCompact_closedBall x.1 1))
  have h2 := (integrable_indicator_iff measurableSet_closedBall).mpr
    ((locallyIntegrable_const (μ := (volume : Measure ℝ)) (1 : ℝ)).integrableOn_isCompact
      (isCompact_closedBall x.2 1))
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  by_cases ha : p.1 ∈ Metric.closedBall x.1 1 <;> by_cases hb : p.2 ∈ Metric.closedBall x.2 1 <;>
    simp [Set.indicator_apply, Set.mem_prod, ha, hb]
end ReciprocityTheory.AnForm.A
