-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:44.775135+00:00
-- url     : https://prove2.me/submissions/aa1076e5-7b4c-4394-9c43-72f902089f4e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_tendsto_mul_pos_22da9efe80ed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
private theorem frequently_filterAt_of_eventually_closedBall (μ : Measure V) [SFinite μ] (x : V) {P : Set V → Prop}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (closedBall x r)) :
    ∃ᶠ a in (Besicovitch.vitaliFamily μ).filterAt x, P a := by
  intro hne
  have h2 := (Besicovitch.tendsto_filterAt μ x).eventually hne
  obtain ⟨r, hr1, hr2⟩ := (h.and h2).exists
  exact hr2 hr1
end Formalism.BasicNotions.Examples₂.CD
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {ε δ : ℝ} (hε1 : ε < 1) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M : ℝ≥0∞) ≤ M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V))
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), nu (closedBall 0 r) ≤ M * lam (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : nu s ≤ M' * lam s := by
  have ha : 0 < 1 - ε := by linarith
  have key : nu s ≤ (M' • lam) s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily nu) (M' • lam)
      MeasureTheory.Measure.AbsolutelyContinuous.rfl s fun x hx => frequently_filterAt_of_eventually_closedBall nu x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr ha)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 - ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 - ε)⁻¹ * ρ := mul_pos (inv_pos.mpr ha) h3
    have hq' := (hq x hx' _ hr h2).1
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x ha.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc nu (closedBall x ρ) ≤ nu (closedBall 0 ((1 - ε)⁻¹ * ρ)) := hq'
      _ ≤ M * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) := h1
      _ ≤ (M' * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 - ε)⁻¹ * ρ)) :=
          by gcongr
      _ = M' * lam (closedBall x ρ) := by rw [e, mul_assoc]
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using key
end Formalism.BasicNotions.Examples₂.CD
