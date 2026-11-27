-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyLelongMono_proof_b5c6405bb597
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:10:47.085086+00:00
-- url     : https://prove2.me/submissions/ad580cf5-e4aa-4d30-9489-f622b51edbda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarWirtinger
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyLelongMono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSetEuc_subsingleton_of_dim_zero_78a54154e23d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_euclBall_iff_5e33abc501c8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace VarietyLelongMono
theorem _root_.solution (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by
  intro n d J hJ hdim z hz r s hr hrs
  rcases d with _ | d
  · have hsub := zeroSetEuc_subsingleton_of_dim_zero J hJ hdim hz
    have hpt : ∀ ρ : ℝ, 0 < ρ → zeroSetEuc J ∩ Metric.ball z ρ = {z} := by
      intro ρ hρ
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => hsub y h.1
      · rintro rfl
        exact ⟨hz, Metric.mem_ball_self hρ⟩
    rw [hpt r hr, hpt s (hr.trans_le hrs)]
    simp [Measure.hausdorffMeasure_zero_singleton]
  · obtain ⟨A, hA⟩ := hN n (d + 1) J hdim
    obtain ⟨c, hc, hWc⟩ := hW d
    have hball : ∀ ρ : ℝ, (fun x : Fin n → ℂ => WithLp.toLp 2 x) ⁻¹' Metric.ball z ρ =
        euclBall (WithLp.ofLp z) ρ := by
      intro ρ
      ext y
      rw [Set.mem_preimage, mem_euclBall_iff, Metric.mem_ball]
    have hμ : ∀ ρ : ℝ, μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) =
        ENNReal.ofReal (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) ρ).indicator fun _ => 1)
          (fun _ => euclPot) y) := by
      intro ρ
      rw [← hball ρ]
      exact (hWc n J A hJ hdim hA _ measurableSet_ball Metric.isBounded_ball).2
    have key := hM n d J A (WithLp.ofLp z) r s hJ hdim hA hr hrs
    rw [hμ r, hμ s, ← ENNReal.ofReal_mul (pow_nonneg (hr.le.trans hrs) _),
      ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc s ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y)
        = c * (s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
      _ ≤ c * (r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := mul_le_mul_of_nonneg_left key hc.le
      _ = r ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
end VarietyLelongMono
end GroundTheory.Heights₂.Heights
