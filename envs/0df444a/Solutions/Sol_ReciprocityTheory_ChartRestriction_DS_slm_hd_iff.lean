-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_hd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:53.384827+00:00
-- url     : https://prove2.me/submissions/e2fe0a77-0ced-48a2-8c7f-2fa1b5895571

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn

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
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {f : ℝ → Matrix (Fin n) (Fin n) ℂ} {f' : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} :
    HasDerivAt f f' s ↔ ∀ i j, HasDerivAt (fun t => f t i j) (f' i j) s := by
  first
  | exact hasDerivAt_pi.trans (forall_congr' fun i => hasDerivAt_pi)
  | exact (hasDerivAt_pi (Φ := f)).trans (forall_congr' fun i => hasDerivAt_pi)
end ReciprocityTheory.ChartRestriction.DS
