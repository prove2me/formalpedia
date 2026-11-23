-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_act_mul__84e45c71f726
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:13.980572+00:00
-- url     : https://prove2.me/submissions/c4646ef4-ecf0-4c1a-8764-01bd5460027a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_act_eq_actE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_mul

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
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (α β : 𝓞 E) (v : Vsp dim) : act (α * β) v = act α (act β v) := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE]
  push_cast
  exact actE_mul _ _ v
end ReciprocityTheory.ChartRestriction.G.I2
