-- Prove2me | solution 1 for PI.RhsWLim.W.scale_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:21.394203+00:00
-- url     : https://prove2.me/submissions/4298a5bd-528e-4cee-810a-f405f1f60473

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_UnimodS
import Theorems.Thm_PI_RhsWLim_W_map_rmul_one
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
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim HU
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (ν : Measure (Mt k r)) (p p' : Mat k r) (hpp : p * p' = 1) (s : Set (Mt k r))
    (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) (c c' : ℝ≥0∞) (hc : ν.map (rmulM p) = c • ν)
    (hc' : ν.map (rmulM p') = c' • ν) : c * c' = 1 := by
  have e : ν = (c * c') • ν := by
    calc ν = ν.map (rmulM (p * p')) := by rw [hpp, map_rmul_one]
      _ = (ν.map (rmulM p)).map (rmulM p') := by
          rw [Measure.map_map (rmulM_meas p') (rmulM_meas p), rmulM_comp]
      _ = (c * c') • ν := by rw [hc, Measure.map_smul, hc', smul_smul]
  have e2 := congrArg (fun m : Measure (Mt k r) => m s) e
  simp only [Measure.smul_apply, smul_eq_mul] at e2
  exact (ENNReal.mul_left_inj h0 ht).1 (show (c * c') * ν s = 1 * ν s by rw [one_mul]; exact e2.symm)
end PI.RhsWLim.W
