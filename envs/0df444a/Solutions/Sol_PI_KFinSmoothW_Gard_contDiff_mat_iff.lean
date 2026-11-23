-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.contDiff_mat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:03.716843+00:00
-- url     : https://prove2.me/submissions/c72d61ad-2736-424f-b278-90cc74125920

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {N : WithTop ℕ∞}
namespace PI.KFinSmoothW.Gard
theorem _root_.solution {f : E → Matrix (Fin n) (Fin n) ℂ} :
    ContDiff ℝ N f ↔ ∀ i j, ContDiff ℝ N (fun x => f x i j) := by
  exact contDiff_pi.trans (forall_congr' fun i => contDiff_pi)
end PI.KFinSmoothW.Gard
