-- Prove2me | solution 1 for PI.IsoInvMetricW.e_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:15.688861+00:00
-- url     : https://prove2.me/submissions/bd495099-0082-45e6-862a-8fbeeb575d6f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Theorems.Thm_PI_IsoInvMetricW_metric_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (g : Lt → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ s, g s = 1) (I J : ColChoice N nu) :
    E nu g I J = if I = J then 1 else 0 := by
  have : g = fun s => Matrix.diagonal (fun _ => (1 : ℂ)) := by
    funext s
    rw [hg, Matrix.diagonal_one]
  rw [this, metric_diagonal]
  split_ifs <;> simp
end PI.IsoInvMetricW
