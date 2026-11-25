-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.prj_Mc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:49.109855+00:00
-- url     : https://prove2.me/submissions/27c57ef6-7b10-4d18-bbf6-a3336c88cbc5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_prj_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_Mc_apply

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
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) (v : Vsp dim) :
    prj σ (Mc σ c v) = c • prj σ v := by
  ext i
  rw [prj_apply, PiLp.smul_apply, prj_apply, Mc_apply, smul_eq_mul]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.I2.ChA
