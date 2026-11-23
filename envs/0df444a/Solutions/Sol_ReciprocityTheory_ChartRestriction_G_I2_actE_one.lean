-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actE_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:59.048801+00:00
-- url     : https://prove2.me/submissions/647d442a-1c58-4ac1-8625-a3dd048cd977

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
theorem _root_.solution (v : Vsp dim) : actE (1 : E) v = v := by
  ext i
  simp
end ReciprocityTheory.ChartRestriction.G.I2
