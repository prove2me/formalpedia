-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.analyticAt_removeNth_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:17.820856+00:00
-- url     : https://prove2.me/submissions/06d36991-7fad-422f-9d66-1860f84fe522

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
theorem _root_.solution {e : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (e + 1)) {F : E → Fin (e + 1) → ℂ} {z : E} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z' => i.removeNth (F z')) z := by
  rw [analyticAt_pi_iff] at hF ⊢
  intro j
  exact hF (i.succAbove j)
end ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts
