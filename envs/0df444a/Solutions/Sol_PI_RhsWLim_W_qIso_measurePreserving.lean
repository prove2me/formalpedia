-- Prove2me | solution 1 for PI.RhsWLim.W.qIso_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:54.433536+00:00
-- url     : https://prove2.me/submissions/c2308537-d5cd-49aa-90dc-c20bfa8ded68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ

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
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) :
    MeasurePreserving (fun x : TrE k => WithLp.ofLp (qFw k x)) volume (volume.prod volume) := by
  exact (WithLp.volume_preserving_ofLp _ _).comp (qIso k).measurePreserving
end PI.RhsWLim.W
