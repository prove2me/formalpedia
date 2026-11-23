-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:24.743584+00:00
-- url     : https://prove2.me/submissions/42918199-0fee-4d3d-9aeb-128640d88147

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {k : WithTop ℕ∞}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiffOn ℝ k f s ↔ ∀ i j, ContDiffOn ℝ k (fun x => f x i j) s := contDiffOn_pi.trans (forall_congr' fun _ => contDiffOn_pi)
end ReciprocityTheory.ChartRestriction.DS
