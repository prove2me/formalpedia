-- Prove2me | solution 1 for PI.RhsWLim.W.haarUniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:14.125494+00:00
-- url     : https://prove2.me/submissions/26baf6f5-aed2-4b38-8599-30e752e0e0c0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Theorems.Thm_PI_RhsWLim_W_HU_map_pull
import Theorems.Thm_PI_RhsWLim_W_HU_pull_apply
import Theorems.Thm_PI_RhsWLim_W_HU_pull_sigmaFinite
import Theorems.Thm_PI_RhsWLim_W_HU_pull_left

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
namespace PI.RhsWLim.W
theorem _root_.solution : HaarUniq := by
  intro k r ν₁ ν₂ hk h1 h2 hB
  obtain ⟨ε, hε, hB⟩ := hB
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := h2
  have i1 : SigmaFinite (pull ν₁) := pull_sigmaFinite ν₁
  have i2 : SigmaFinite (pull ν₂) := pull_sigmaFinite ν₂
  have i3 : (pull ν₁).IsMulLeftInvariant := pull_left ν₁ hl1
  have i4 : (pull ν₂).IsMulLeftInvariant := pull_left ν₂ hl2
  obtain ⟨hb1, hb2, hb3⟩ := hB (ε / 2) (half_pos hε) (half_lt_self hε)
  have key := measure_eq_div_smul (pull ν₁) (pull ν₂) (s := inc ⁻¹' bBall k r (ε / 2))
    (by rw [pull_apply ν₂ hc2]; exact hb2.ne') (by rw [pull_apply ν₂ hc2]; exact hb3.ne)
  refine ⟨pull ν₁ (inc ⁻¹' bBall k r (ε / 2)) / pull ν₂ (inc ⁻¹' bBall k r (ε / 2)), ?_, ?_⟩
  · rw [pull_apply ν₁ hc1, pull_apply ν₂ hc2]
    exact (ENNReal.div_lt_top hb1.ne hb2.ne').ne
  · calc ν₁ = (pull ν₁).map inc := (map_pull ν₁ hc1).symm
      _ = ((pull ν₁ (inc ⁻¹' bBall k r (ε / 2)) / pull ν₂ (inc ⁻¹' bBall k r (ε / 2))) • pull ν₂).map inc := by
          rw [← key]
      _ = _ := by rw [Measure.map_smul, map_pull ν₂ hc2]
end PI.RhsWLim.W
