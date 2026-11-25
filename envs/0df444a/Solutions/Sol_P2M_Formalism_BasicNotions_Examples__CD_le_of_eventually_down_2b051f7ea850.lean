-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:34.670752+00:00
-- url     : https://prove2.me/submissions/0f64a5fa-cc2f-4f5e-a764-ce577ef45a90

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
theorem _root_.solution {ε δ : ℝ} (hε0 : 0 < ε) (hq : QInv nu ε δ) (M M' : ℝ≥0)
    (hM : (M' : ℝ≥0∞) * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) ≤ M)
    (hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), M * lam (closedBall 0 r) ≤ nu (closedBall 0 r))
    (s : Set V) (hs : s ⊆ ball 0 δ) : M' * lam s ≤ nu s := by
  have hb : 0 < 1 + ε := by linarith
  have key : ((M' : ℝ≥0∞) • lam) s ≤ nu s := by
    refine VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily lam) nu
      (Measure.smul_absolutelyContinuous) s fun x hx => frequently_filterAt_of_eventually_closedBall lam x ?_
    have hx' : ‖x‖ < δ := mem_ball_zero_iff.mp (hs hx)
    have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg x) hx'
    have ht := tendsto_mul_pos (inv_pos.mpr hb)
    have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (1 + ε)⁻¹ * ρ < δ :=
      (ht.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
    filter_upwards [ht.eventually hev, hsmall, self_mem_nhdsWithin] with ρ h1 h2 h3
    have hr : 0 < (1 + ε)⁻¹ * ρ := mul_pos (inv_pos.mpr hb) h3
    have hq' := (hq x hx' _ hr h2).2
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hq'
    have e := Measure.addHaar_closedBall_mul lam x hb.le hr.le
    rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at e
    simp only [Measure.smul_apply, smul_eq_mul]
    calc (M' : ℝ≥0∞) * lam (closedBall x ρ)
        = (M' * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V)) * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by
          rw [e, mul_assoc]
      _ ≤ M * lam (closedBall 0 ((1 + ε)⁻¹ * ρ)) := by gcongr
      _ ≤ nu (closedBall 0 ((1 + ε)⁻¹ * ρ)) := h1
      _ ≤ nu (closedBall x ρ) := hq'
  simpa only [Measure.smul_apply, smul_eq_mul] using key
end Formalism.BasicNotions.Examples₂.CD
