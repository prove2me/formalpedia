-- Prove2me | solution 1 for PI.IsoInvMetricW.symmetricMeasure_l2Norm_eq_resolutionL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:57.532098+00:00
-- url     : https://prove2.me/submissions/500d6824-8ceb-412d-bb1a-826f003927a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_SymmetricMeasureL2NormEqResolutionL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (φ : LaC N nu) : ((l2 φ : ℝ) : ℂ) = ipl φ φ := by
  unfold l2 ipl
  rw [finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
end PI.IsoInvMetricW
