-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:35:38.736363+00:00
-- url     : https://prove2.me/submissions/2081574a-3544-4291-9d90-526ce5445610

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pow
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
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (h : w a = m) (z : ℤ) :
    w (a ^ z) = ((z * m : ℤ) : WithTop ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [zpow_natCast, wa_pow w h n]
  · rw [zpow_neg, zpow_natCast, wa_inv w (wa_pow w h n)]
    congr 1
    ring
end ReciprocityTheory.ChartRestriction.G.T0
