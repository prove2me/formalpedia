-- Prove2me | solution 1 for PI.RhsWLim.W.unimodW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:08.736496+00:00
-- url     : https://prove2.me/submissions/d7a392a8-3dcd-428c-a6dd-4f64e2f557f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Theorems.Thm_PI_RhsWLim_W_rmulM_comp
import Theorems.Thm_PI_RhsWLim_W_rmulM_meas

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
theorem _root_.solution (hU : UnitInv) (hH : HermInv) (hP : PolarDecW) : UnimodW := by
  intro k r ν hk hG p hp
  obtain ⟨B₀, hB, hBh, q, hq, hqu, rfl⟩ := hP k r p hp
  rw [← rmulM_comp, ← Measure.map_map (rmulM_meas q) (rmulM_meas _), hH k r ν hk hG B₀ hB hBh,
    hU k r ν hk hG q hq hqu]
end PI.RhsWLim.W
