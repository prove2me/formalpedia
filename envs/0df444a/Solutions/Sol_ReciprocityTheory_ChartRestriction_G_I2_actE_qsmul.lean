-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actE_qsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:31.900138+00:00
-- url     : https://prove2.me/submissions/8032db1c-a466-43f8-9e1c-a6636cc11336

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (q : ℚ) (β : E) (v : Vsp dim) : actE (q • β) v = (q : ℝ) • actE β v := by
  ext i
  simp only [actE_apply, PiLp.smul_apply, Complex.real_smul, Rat.smul_def, map_mul, map_ratCast,
    Complex.ofReal_ratCast]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
