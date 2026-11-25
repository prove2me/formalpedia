-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:33:56.051963+00:00
-- url     : https://prove2.me/submissions/9af1448b-ca3e-411b-b942-ce6fbbc09689

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv

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
    (hb : w b = n) : w (a / b) = ((m - n : ℤ) : WithTop ℤ) := by
  rw [div_eq_mul_inv, wa_mul w ha (wa_inv w hb), sub_eq_add_neg]
end ReciprocityTheory.ChartRestriction.G.T0
