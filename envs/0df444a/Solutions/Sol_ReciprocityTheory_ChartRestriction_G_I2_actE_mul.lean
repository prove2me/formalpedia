-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actE_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:41.646239+00:00
-- url     : https://prove2.me/submissions/3c4ddb13-0701-48f3-be21-12125d32491f

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
theorem _root_.solution (β γ : E) (v : Vsp dim) : actE (β * γ) v = actE β (actE γ v) := by
  ext i
  simp [mul_assoc]
end ReciprocityTheory.ChartRestriction.G.I2
