-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.Av_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:21.623686+00:00
-- url     : https://prove2.me/submissions/0d020c7a-d1c0-4c78-9be4-15b6766da85b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_shift_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Av_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_Av_line

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
theorem _root_.solution (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (hp : IPer Ψ) (w : Fin k → ℂ) :
    Av Ψ w = Av Ψ 0 := by
  have hdec : w = rl (fun i => (w i).re) + ∑ l, (((w l).im : ℂ) * I) • (Pi.single l 1 : Fin k → ℂ) := by
    funext i; simp [rl, Finset.sum_apply, Pi.single_apply, Complex.re_add_im]
  rw [hdec, shift_sum (Av Ψ) _ (fun l v => Av_line Ψ hd hp v l _)]
  have := Av_real Ψ hd.continuous hp 0 (fun i => (w i).re)
  rwa [zero_add] at this
end ReciprocityTheory.ChartRestriction.G.I2.DimB
