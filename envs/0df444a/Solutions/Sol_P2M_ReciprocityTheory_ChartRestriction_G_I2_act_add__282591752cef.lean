-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_act_add__282591752cef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:42.88183+00:00
-- url     : https://prove2.me/submissions/51ae3348-4df0-4624-bc30-e2c6a257e4f3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_act_eq_actE


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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  rw [act_eq_actE, act_eq_actE, act_eq_actE, actE_add_right]
end ReciprocityTheory.ChartRestriction.G.I2
