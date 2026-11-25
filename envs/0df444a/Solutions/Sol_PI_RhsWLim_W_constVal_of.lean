-- Prove2me | solution 1 for PI.RhsWLim.W.constVal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:45.158155+00:00
-- url     : https://prove2.me/submissions/62b35979-d359-416b-bad1-b120f9add7b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstCut
import Theorems.Thm_PI_RhsWLim_W_volU_pos
import Theorems.Thm_PI_RhsWLim_W_continuous_pairF
import Theorems.Thm_PI_RhsWLim_W_gauge_of_lim
import Theorems.Thm_PI_RhsWLim_W_annU_open
import Theorems.Thm_PI_RhsWLim_W_testJ

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
theorem _root_.solution (hR : RhsTest) (hP : PairPush) : ConstVal := by
  intro k r z z' μW μW' a a' μsec hW νg c hH hL hrep
  have hg := gauge_of_lim νg hH hL
  have hT := hW.T_pos
  have hT' := hW.T'_pos
  have hTT : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator (annU_open _ _).measurableSet
  have hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)
      (pairF k r z z' x)) := hgm.comp (continuous_pairF k r z z').measurable
  have h1 := hR k r z z' μW μW' a a' μsec hW _ hgm
  have h2 := hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm
  have h3 := hrep _ hφm
  obtain ⟨hJ0, hJt⟩ := testJ k (Tz k r z) (Tz k r z') hTT
  rw [h3, h2, ← mul_assoc] at h1

  have h4 := (ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1
  have hv := volU_pos k
  have hv1 := volU_pos (k - 1)
  have hpc : 0 < pairConst k (Tz k r z) (Tz k r z') := by
    unfold pairConst
    positivity
  have ha := hW.a_pos
  have ha' := hW.a'_pos
  have h5 := congrArg ENNReal.toReal h4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)] at h5
  have hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z') := by
    rw [← h5]
    field_simp
  rw [hc]
  unfold pairConst wbConst
  have hTk : 0 < (Tz k r z * Tz k r z') ^ k := pow_pos hTT k
  field_simp
end PI.RhsWLim.W
