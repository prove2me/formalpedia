-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:37:50.687156+00:00
-- url     : https://prove2.me/submissions/191aa6ac-c3d5-43dd-9716-c48c30e42bc2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_eq_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (v w : AddValuation F (WithTop ℤ)) (hv : ∀ a : F, a ≠ 0 → v a ≠ ⊤)
    (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) (hv1 : ∃ π : F, v π = 1) (hw1 : ∃ ρ : F, w ρ = 1)
    (hne : v ≠ w) : ∃ s, 0 < v s ∧ w s < 0 := by
  by_contra hcon
  push_neg at hcon
  exact hne (wa_eq_of_le v w hv hw hv1 hw1 hcon)
end ReciprocityTheory.ChartRestriction.G.T0
