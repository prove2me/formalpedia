-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.IsU.norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:50.715624+00:00
-- url     : https://prove2.me/submissions/c082135e-f93c-4bf4-8fea-f42334d2f982

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA

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
namespace IsU
theorem _root_.solution {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (h : IsU I x u) :
    ‖u‖ ^ 2 = (Hf x u).im := by
  rw [← real_inner_self_eq_norm_sq, h.2 u h.1]
end IsU
end ReciprocityTheory.ChartRestriction.G.I2
