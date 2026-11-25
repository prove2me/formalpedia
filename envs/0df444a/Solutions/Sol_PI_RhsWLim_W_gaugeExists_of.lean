-- Prove2me | solution 1 for PI.RhsWLim.W.gaugeExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:09.081442+00:00
-- url     : https://prove2.me/submissions/83d6ff22-7dfc-4b7e-a7cc-58c6540819f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ChartLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_GaugeExists
import Theorems.Thm_PI_RhsWLim_W_bBall_eq
import Theorems.Thm_PI_RhsWLim_W_GE_lie_nontrivial
import Theorems.Thm_PI_RhsWLim_W_GE_haarOn_smul
import Theorems.Thm_PI_RhsWLim_W_GE_tBall_mass

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
open scoped ENNReal NNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open GE
namespace PI.RhsWLim.W
theorem _root_.solution (hH : HaarDens) (hL : ChartLim) : GaugeExists := by
  intro k r hk
  obtain ⟨νh, hνh, δ, hδc, hδ0, hδt, ε, hε, hball⟩ := hH k r hk
  set c : ℝ≥0 := ((δ 0).toNNReal)⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero (ENNReal.toNNReal_pos hδ0 hδt).ne'
  have hg : IsHaarOn (UWb k r) (c • νh) := haarOn_smul _ _ c hc hνh
  have hup : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ x < δ 0 + 1 :=
    hδc.eventually (gt_mem_nhds (ENNReal.lt_add_right hδt one_ne_zero))
  have hlo : ∀ᶠ x in 𝓝 (0 : lieE (UWb k r)), δ 0 / 2 < δ x :=
    hδc.eventually (lt_mem_nhds (ENNReal.half_lt_self hδ0 hδt))
  obtain ⟨ε', hε', hε'b⟩ := Metric.eventually_nhds_iff.mp (hup.and hlo)
  refine ⟨c • νh, hg, ⟨min ε ε', lt_min hε hε', fun ρ hρ hρε => ?_⟩, fun m hm => ?_⟩
  · have hρ1 : ρ < ε := hρε.trans_le (min_le_left _ _)
    have hρ2 : ρ < ε' := hρε.trans_le (min_le_right _ _)
    have hbd : ∀ x ∈ Metric.ball (0 : lieE (UWb k r)) ρ, δ x < δ 0 + 1 ∧ δ 0 / 2 < δ x :=
      fun x hx => hε'b ((Metric.mem_ball.mp hx).trans hρ2)
    have hmeas : MeasurableSet (Metric.ball (0 : lieE (UWb k r)) ρ) := measurableSet_ball
    have hvpos : 0 < volume (Metric.ball (0 : lieE (UWb k r)) ρ) := Metric.measure_ball_pos _ _ hρ
    have hvfin : volume (Metric.ball (0 : lieE (UWb k r)) ρ) < ⊤ := measure_ball_lt_top
    have hI : νh (bBall k r ρ) = ∫⁻ x in Metric.ball 0 ρ, δ x := hball ρ hρ hρ1
    have hlow : δ 0 / 2 * volume (Metric.ball (0 : lieE (UWb k r)) ρ) ≤ νh (bBall k r ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).2.le
    have hhigh : νh (bBall k r ρ) ≤ (δ 0 + 1) * volume (Metric.ball (0 : lieE (UWb k r)) ρ) := by
      rw [hI, ← setLIntegral_const]
      exact setLIntegral_mono' hmeas fun x hx => (hbd x hx).1.le
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    constructor
    · exact ENNReal.mul_pos (by exact_mod_cast hc)
        (lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.half_pos hδ0).ne' hvpos.ne') hlow).ne'
    · exact ENNReal.mul_lt_top ENNReal.coe_lt_top
        (lt_of_le_of_lt hhigh (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hδt.lt_top, ENNReal.one_lt_top⟩) hvfin))
  · have := lie_nontrivial (k := k) (r := r)
    have hlim := hL (lieE (UWb k r)) (Mt k r) (expC k r) νh δ hδc hδt
      ⟨ε, hε, fun ρ h1 h2 => by rw [← bBall_eq]; exact hball ρ h1 h2⟩
    have key : (fun ρ : ℝ => ((c • νh) (tBall k r m ρ)).toReal / bVol k r ρ) = fun ρ => (c : ℝ) *
        ((νh (expC k r '' Metric.ball 0 ρ)).toReal / (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal) := by
      funext ρ
      rw [tBall_mass _ hg m hm ρ, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul, bBall_eq,
        bVol, mul_div_assoc]
    have h1 : (c : ℝ) * (δ 0).toReal = 1 := by
      rw [hcdef, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal]
      exact inv_mul_cancel₀ (ENNReal.toReal_pos hδ0 hδt).ne'
    rw [key]
    have h2 := hlim.const_mul (c : ℝ)
    rwa [h1] at h2
end PI.RhsWLim.W
