-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:45.464294+00:00
-- url     : https://prove2.me/submissions/569f3ed6-1fc0-425d-aca5-ebfe9affa601

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_measurePreserving_circle_smul_8915803838c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {D : ℕ} (u : Circle) (ρ : ℝ) (F : (Fin D → ℂ) → ℂ) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, F ((u : ℂ) • z) =
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, F z := by
  have he : MeasurableEmbedding (fun z : Fin D → ℂ => (u : ℂ) • z) :=
    (Homeomorph.smulOfNeZero (u : ℂ) (Circle.coe_ne_zero u)).measurableEmbedding
  rw [← (measurePreserving_circle_smul u).setIntegral_preimage_emb he F]
  have hpre : (fun z : Fin D → ℂ => (u : ℂ) • z) ⁻¹' closedBall 0 ρ = closedBall 0 ρ := by
    ext z
    simp [norm_smul, Circle.norm_coe]
  rw [hpre]
end GroundTheory.Heights₂.Heights.HilbertSamuel
