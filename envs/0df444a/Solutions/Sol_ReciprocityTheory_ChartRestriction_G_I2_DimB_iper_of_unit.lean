-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.iper_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:36.565802+00:00
-- url     : https://prove2.me/submissions/76f4f2bf-fafa-433d-ab61-1b0515406533

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_shift_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_shift_int

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
theorem _root_.solution (Ψ : (Fin k → ℂ) → ℂ) (h : ∀ l z, Ψ (z + Pi.single l 1) = Ψ z) : IPer Ψ := by
  intro n z
  have hn : iz n = ∑ l, (n l) • (Pi.single l 1 : Fin k → ℂ) := by
    funext i; simp [iz, Finset.sum_apply, Pi.single_apply]
  rw [hn]
  exact shift_sum Ψ _ (fun l v => shift_int Ψ _ (h l) (n l) v) _ z
end ReciprocityTheory.ChartRestriction.G.I2.DimB
