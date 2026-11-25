-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.chord_norm_y_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:42:44.801911+00:00
-- url     : https://prove2.me/submissions/049a89be-ee5e-48ff-a3e1-634067877191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_norm_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (W : WeierstrassCurve C) (hW : IntegralModel W) {x y : C}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  rw [Affine.equation_iff] at h
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hx
  have e2 : ‖W.a₂ * x ^ 2‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖W.a₂‖ * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2]
  have e4 : ‖W.a₄ * x‖ < ‖x ^ 3‖ := by
    rw [norm_mul, norm_pow]
    calc ‖W.a₄‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ < ‖x‖ ^ 3 := by nlinarith [pow_pos hx0 2, mul_pos hx0 hx0]
  have e6 : ‖W.a₆‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    calc ‖W.a₆‖ ≤ 1 := h6
      _ < ‖x‖ ^ 3 := one_lt_pow₀ hx (by norm_num)
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ = ‖x‖ ^ 3 := by
    have s1 := chord_norm_add e2
    have s2 : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x‖ = ‖x ^ 3‖ := by
      rw [chord_norm_add (by rw [s1]; exact e4), s1]
    rw [chord_norm_add (by rw [s2]; exact e6), s2, norm_pow]
  have hL : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
  rw [← h, hL, norm_mul] at hR
  have hc : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3.trans hx.le))
    rw [norm_mul]
    calc ‖W.a₁‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  have hyx : ‖x‖ < ‖y‖ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hs : ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcon hc)
    have : ‖y‖ * ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul hcon hs (norm_nonneg _) hx0.le
    nlinarith [mul_pos hx0 hx0]
  rw [chord_norm_add (lt_of_le_of_lt hc hyx)] at hR
  rw [← hR]; ring
end ReciprocityTheory.ChartRestriction.L1
