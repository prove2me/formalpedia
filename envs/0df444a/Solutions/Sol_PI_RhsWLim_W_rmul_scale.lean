-- Prove2me | solution 1 for PI.RhsWLim.W.rmul_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:26:02.742272+00:00
-- url     : https://prove2.me/submissions/a4c891f9-cfcc-4d61-aa6a-617696210916

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
import Theorems.Thm_PI_RhsWLim_W_rmul_haar
import Theorems.Thm_PI_RhsWLim_W_HU_map_pull
import Theorems.Thm_PI_RhsWLim_W_HU_pull_apply
import Theorems.Thm_PI_RhsWLim_W_HU_pull_left
import Theorems.Thm_PI_RhsWLim_W_HU_pull_sigmaFinite


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
theorem _root_.solution (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r)
    (s : Set (Mt k r)) (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) :
    ν.map (rmulM p) = (ν.map (rmulM p) s / ν s) • ν := by
  have h1 := rmul_haar ν hH p hp
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := hH
  have i1 : SigmaFinite (pull (ν.map (rmulM p))) := pull_sigmaFinite _
  have i2 : SigmaFinite (pull ν) := pull_sigmaFinite ν
  have i3 : (pull (ν.map (rmulM p))).IsMulLeftInvariant := pull_left _ hl1
  have i4 : (pull ν).IsMulLeftInvariant := pull_left ν hl2
  have key := measure_eq_div_smul (pull (ν.map (rmulM p))) (pull ν) (s := inc ⁻¹' s)
    (by rw [pull_apply ν hc2]; exact h0) (by rw [pull_apply ν hc2]; exact ht)
  calc ν.map (rmulM p) = (pull (ν.map (rmulM p))).map inc := (map_pull _ hc1).symm
    _ = ((pull (ν.map (rmulM p)) (inc ⁻¹' s) / pull ν (inc ⁻¹' s)) • pull ν).map inc := by rw [← key]
    _ = _ := by rw [Measure.map_smul, map_pull ν hc2, pull_apply _ hc1, pull_apply ν hc2]
end PI.RhsWLim.W
