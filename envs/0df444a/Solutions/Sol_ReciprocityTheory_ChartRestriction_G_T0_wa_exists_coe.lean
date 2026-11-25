-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_exists_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:49.745427+00:00
-- url     : https://prove2.me/submissions/1fabcd96-5082-41b0-86ce-3b55c08c0b66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox

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
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) {a : F}
    (ha : a ≠ 0) : ∃ m : ℤ, w a = m := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hw a ha)
  exact ⟨m, hm.symm⟩
end ReciprocityTheory.ChartRestriction.G.T0
