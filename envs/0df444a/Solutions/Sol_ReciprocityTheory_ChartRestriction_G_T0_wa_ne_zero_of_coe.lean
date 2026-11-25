-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_ne_zero_of_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:52.801883+00:00
-- url     : https://prove2.me/submissions/14d00d78-8e7e-4abd-b03d-2902f58496cb

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
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) :
    a ≠ 0 := by
  rintro rfl
  rw [AddValuation.map_zero] at h
  exact WithTop.top_ne_coe h
end ReciprocityTheory.ChartRestriction.G.T0
