-- Prove2me | solution 1 for PI.RhsWLim.W.mBaseMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:17:23.63425+00:00
-- url     : https://prove2.me/submissions/4369fdfa-e5ba-4be5-a8b9-3ac9e0560f95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mem_UWb

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
theorem _root_.solution : MBaseMem := by
  intro k r z z' μW μW' a a' μsec hD
  have hT := hD.T_pos
  have hT' := hD.T'_pos
  have hp : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hζ : Tz k r z * Tz k r z' < Complex.normSq (zeta0 k r z z') := by
    unfold zeta0
    rw [Complex.normSq_ofReal]
    have hs : Real.sqrt (Tz k r z * Tz k r z') * Real.sqrt (Tz k r z * Tz k r z') = Tz k r z * Tz k r z' :=
      Real.mul_self_sqrt hp.le
    nlinarith
  exact MB.emb_mem_UWb (hD.sec.2 _ hζ).1
end PI.RhsWLim.W
