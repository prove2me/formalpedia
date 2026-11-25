-- Prove2me | solution 1 for PI.RhsWLim.W.MB.mulVec_bvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:54.931459+00:00
-- url     : https://prove2.me/submissions/ef9aae01-c9c3-4cbc-b284-eb3ee47dfa10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.MB
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) : (A *ᵥ bvec j) l = A l j := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end PI.RhsWLim.W.MB
