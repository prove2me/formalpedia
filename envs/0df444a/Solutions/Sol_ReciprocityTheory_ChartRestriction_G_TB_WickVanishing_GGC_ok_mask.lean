-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.ok_mask
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:38.561063+00:00
-- url     : https://prove2.me/submissions/a95031b4-eeff-4055-a134-bcdd8723e099

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_mask_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ok p0 (mask p0 t y) := by
  have hs : conj ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) = 1 - (t : ℂ) ^ 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
    push_cast
    ring
  unfold Ok
  rw [mask_eq h t _ hs]
  exact h.add_posSemidef (posSemidef_conjTranspose_mul_self _)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
