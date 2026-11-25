-- Prove2me | solution 1 for PositivityTheory.RL.Up.norm_le_of_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:43.222124+00:00
-- url     : https://prove2.me/submissions/adfed6a3-4836-4e3a-8d4c-88375d9e3302

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
namespace PositivityTheory.RL.Up
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (g : V → ℂ) (hg : Continuous g) {C : ℝ} (x : V)
    (h : ∀ r > 0, ‖∫ y in Metric.closedBall x r, g y ∂μ‖ ≤ C * μ.real (Metric.closedBall x r)) : ‖g x‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.1 (hg.continuousAt (x := x)) ε hε
  have hr : 0 < δ / 2 := by positivity
  set s := Metric.closedBall x (δ / 2)
  have hfin : μ s < ⊤ := (isCompact_closedBall x _).measure_lt_top
  have hpos : 0 < μ.real s := ENNReal.toReal_pos (Metric.measure_closedBall_pos μ x hr).ne' hfin.ne
  have h1 : ‖∫ y in s, (g x - g y) ∂μ‖ ≤ ε * μ.real s :=
    norm_setIntegral_le_of_norm_le_const hfin fun y hy => by
      rw [← dist_eq_norm, dist_comm]
      exact (hd (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith))).le
  rw [integral_sub (show IntegrableOn (fun _ => g x) s μ from integrableOn_const hfin.ne) (hg.continuousOn.integrableOn_compact (isCompact_closedBall x _)),
    setIntegral_const] at h1
  have h2 := h _ hr
  have h3 : ‖μ.real s • g x‖ ≤ (C + ε) * μ.real s := by
    have := norm_add_le (μ.real s • g x - ∫ y in s, g y ∂μ) (∫ y in s, g y ∂μ)
    rw [sub_add_cancel] at this
    linarith
  rw [norm_smul, Real.norm_of_nonneg hpos.le, mul_comm] at h3
  exact le_of_mul_le_mul_right h3 hpos
end PositivityTheory.RL.Up
