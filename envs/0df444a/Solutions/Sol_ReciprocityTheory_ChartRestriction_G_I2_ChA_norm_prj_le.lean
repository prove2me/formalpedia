-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.norm_prj_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:45.048889+00:00
-- url     : https://prove2.me/submissions/d7ec421d-8829-46d5-a139-9ba2c4bf6a2f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_prj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : ‖prj σ v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [prj_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    positivity
end ReciprocityTheory.ChartRestriction.G.I2.ChA
