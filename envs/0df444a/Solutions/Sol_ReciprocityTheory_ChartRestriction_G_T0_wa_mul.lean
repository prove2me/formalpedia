-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:54.879621+00:00
-- url     : https://prove2.me/submissions/c19a306d-d587-428f-80c8-06dac051c503

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
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) {a b : F} {m n : ℤ} (ha : w a = m)
    (hb : w b = n) : w (a * b) = ((m + n : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_mul, ha, hb, ← WithTop.coe_add]
end ReciprocityTheory.ChartRestriction.G.T0
