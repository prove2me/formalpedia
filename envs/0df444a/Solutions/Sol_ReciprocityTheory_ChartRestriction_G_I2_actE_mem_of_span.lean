-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.actE_mem_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:59.637808+00:00
-- url     : https://prove2.me/submissions/5ec8e524-713d-4659-9be0-9a2d2dc623f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_rsmul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_zero_right

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
theorem _root_.solution (β : E) (S : Set (Vsp dim)) (T : Submodule ℝ (Vsp dim))
    (h : ∀ v ∈ S, actE β v ∈ T) : ∀ v ∈ Submodule.span ℝ S, actE β v ∈ T := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [actE_zero_right]; exact T.zero_mem
  | add x y _ _ hx hy => rw [actE_add_right]; exact T.add_mem hx hy
  | smul r x _ hx => rw [actE_rsmul_right]; exact T.smul_mem r hx
end ReciprocityTheory.ChartRestriction.G.I2
