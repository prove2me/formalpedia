-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:09.554183+00:00
-- url     : https://prove2.me/submissions/bcd53c81-8df9-421a-9bda-c4fa6eb04da9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe

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
theorem _root_.solution (w : AddValuation F (WithTop ℤ)) {a : F} {m : ℤ} (ha : w a = m) :
    w a⁻¹ = ((-m : ℤ) : WithTop ℤ) := by
  have ha0 : a ≠ 0 := wa_ne_zero_of_coe w ha
  have h1 : w (a⁻¹ * a) = 0 := by rw [inv_mul_cancel₀ ha0, AddValuation.map_one]
  rw [AddValuation.map_mul, ha] at h1
  have hne : w a⁻¹ ≠ ⊤ := by
    intro ht
    rw [ht, WithTop.top_add, ← WithTop.coe_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hc] at h1 ⊢
  have h2 : c + m = 0 := by exact_mod_cast h1
  rw [show c = -m by omega]
end ReciprocityTheory.ChartRestriction.G.T0
