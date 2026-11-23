-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_actE__3dabe342590f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:33.225148+00:00
-- url     : https://prove2.me/submissions/31201e4a-dcb4-4baf-a890-e74f3e0b41cb

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
variable [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (β : E) (v w : Vsp dim) :
    Hf v (actE β w) = Hf (actE (IsCMField.complexConj E β) v) w := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [actE_apply, map_mul, IsCMField.complexEmbedding_complexConj]
  ring
end ReciprocityTheory.ChartRestriction.G.I2
