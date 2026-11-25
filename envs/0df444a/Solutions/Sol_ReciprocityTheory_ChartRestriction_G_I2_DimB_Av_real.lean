-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.Av_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:03.705066+00:00
-- url     : https://prove2.me/submissions/e882bfa0-d1fb-4fcb-8e96-d06639e6a138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_box_shift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_rl_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_continuous_rl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (Ψ : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (hp : IPer Ψ) (w : Fin k → ℂ)
    (s : Fin k → ℝ) : Av Ψ (w + rl s) = Av Ψ w := by
  have e : ∀ x, rl x + (w + rl s) = rl (x + s) + w := fun x => by rw [rl_add]; abel
  unfold Av
  simp_rw [e]
  refine box_shift (fun x => Ψ (rl x + w)) (hc.comp (continuous_rl.add continuous_const))
    (fun n t => ?_) s
  have : rl (t + fun i => (n i : ℝ)) + w = (rl t + w) + iz n := by
    rw [rl_add]; have : rl (fun i => (n i : ℝ)) = iz n := by funext i; simp [rl, iz]
    rw [this]; abel
  simp only [this, hp n]
end ReciprocityTheory.ChartRestriction.G.I2.DimB
