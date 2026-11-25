-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:46.269187+00:00
-- url     : https://prove2.me/submissions/5820b2af-3d59-460e-a9f7-a4b4f12c1aac

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
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hq : QInv nu ε δ) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧
      limsup (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤
        ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L ∧
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L ≤
        liminf (fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
  have hae := Besicovitch.ae_tendsto_rnDeriv nu lam
  have hfin := Measure.rnDeriv_lt_top nu lam
  have hpos : lam (ball (0 : V) δ) ≠ 0 := (measure_ball_pos lam 0 hδ).ne'
  obtain ⟨X, hX, hXt, hXf⟩ : ∃ X ∈ ball (0 : V) δ,
      Tendsto (fun r => nu (closedBall X r) / lam (closedBall X r)) (𝓝[>] 0) (𝓝 (nu.rnDeriv lam X)) ∧
        nu.rnDeriv lam X < ⊤ := by
    by_contra hcon
    apply hpos
    have h3 := ae_iff.mp (hae.and hfin)
    refine measure_mono_null (fun y hy => ?_) h3
    show ¬ _
    exact fun h => hcon ⟨y, hy, h.1, h.2⟩
  have hXn : ‖X‖ < δ := mem_ball_zero_iff.mp hX
  have key : ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r →
      nu (closedBall X (t * r)) / lam (closedBall 0 r) =
        ENNReal.ofReal (t ^ finrank ℝ V) * (nu (closedBall X (t * r)) / lam (closedBall X (t * r))) := by
    intro t ht r hr
    rw [Measure.addHaar_closedBall_mul lam X ht.le hr.le, ← mul_div_assoc, ENNReal.mul_div_mul_left]
    · exact (ENNReal.ofReal_pos.mpr (pow_pos ht _)).ne'
    · exact ENNReal.ofReal_ne_top
  have hup : Tendsto (fun r => ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 + ε) * r)) / lam (closedBall X ((1 + ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hlo : Tendsto (fun r => ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) *
      (nu (closedBall X ((1 - ε) * r)) / lam (closedBall X ((1 - ε) * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * nu.rnDeriv lam X)) :=
    ENNReal.Tendsto.const_mul (hXt.comp (tendsto_mul_pos (by linarith))) (Or.inr ENNReal.ofReal_ne_top)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hδ)] with r h0 h1
    exact ⟨h0, h1⟩
  refine ⟨nu.rnDeriv lam X, hXf.ne, ?_, ?_⟩
  · refine (Filter.limsup_le_limsup ?_).trans hup.limsup_eq.le
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).2 _
  · refine hlo.liminf_eq.ge.trans (Filter.liminf_le_liminf ?_)
    filter_upwards [hev] with r hr
    rw [← key _ (by linarith) r hr.1]
    exact ENNReal.div_le_div_right (hq X hXn r hr.1 hr.2).1 _
end Formalism.BasicNotions.Examples₂.CD
