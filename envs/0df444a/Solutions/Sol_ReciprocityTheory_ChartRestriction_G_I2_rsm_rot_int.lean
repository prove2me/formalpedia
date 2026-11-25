-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.rsm_rot_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:12.99618+00:00
-- url     : https://prove2.me/submissions/40c529e1-e897-4b0f-9e0b-8dd8c60be1d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F (u • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by
  have hcoe : ∀ z, rsmRot N u hu z = u • z := fun z => rfl
  have hmp : MeasurePreserving (rsmRot N u hu) := (rsmRot N u hu).measurePreserving
  have hemb : MeasurableEmbedding (rsmRot N u hu) := by
    first
      | exact (rsmRot N u hu).toHomeomorph.measurableEmbedding
      | exact (rsmRot N u hu).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hpre : (rsmRot N u hu) ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext z
    simp [hcoe, norm_smul, hu]
  calc ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F (u • z)‖ ^ 2
      = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r,
          (fun w => Real.exp (-‖w‖ ^ 2) * ‖F w‖ ^ 2) (rsmRot N u hu z) := by
        congr 1
        ext z
        simp only [hcoe, norm_smul, hu, one_mul]
    _ = ∫ z in closedBall (0 : EuclideanSpace ℂ (Fin N)) r, Real.exp (-‖z‖ ^ 2) * ‖F z‖ ^ 2 := by
        have key := hmp.setIntegral_preimage_emb hemb
          (fun w => Real.exp (-‖w‖ ^ 2) * ‖F w‖ ^ 2) (closedBall 0 r)
        rw [hpre] at key
        exact key
end ReciprocityTheory.ChartRestriction.G.I2
