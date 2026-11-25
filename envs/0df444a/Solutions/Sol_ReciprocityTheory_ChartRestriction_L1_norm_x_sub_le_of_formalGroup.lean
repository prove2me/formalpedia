-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_x_sub_le_of_formalGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:05:10.426193+00:00
-- url     : https://prove2.me/submissions/5039c244-3c46-4e55-aea4-af04880c6c7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorClose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_chord_identity
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hb0


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
theorem _root_.solution (W : WeierstrassCurve C) (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3 : W.a₃ = 0)
    (hW : IntegralModel W) (A B : W.toAffine.Point) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAy : ‖py W A‖ ≤ 1) (hBy : ‖py W B‖ ≤ 1) (hs : A + B ≠ 0) (hsx : ‖px W (A + B)‖ ≤ 1)
    (hd : A - B ≠ 0) (hdx : InFormalGroupPoints (A - B)) : ‖px W A - px W B‖ ≤ ‖uOf (A - B)‖ := by
  obtain ⟨-, -, -, h4, h6⟩ := hW
  have hc := chord_identity W h1 h2 h3 A B hA hB hs hd
  generalize A - B = D at hc hd hdx ⊢
  rcases D with _ | ⟨xd, yd, hdn⟩
  · exact absurd rfl hd
  have hX : 1 < ‖xd‖ := hdx
  have hX0 : 0 < ‖xd‖ := by linarith
  have hXne : ‖xd‖ ≠ 0 := hX0.ne'
  have hc' : (px W A - px W B) ^ 2 * (px W (A + B) - xd) = -4 * py W A * py W B := hc
  have eqd := (WeierstrassCurve.Affine.equation_iff _ _).1 hdn.1
  have e : yd ^ 2 = xd ^ 3 + (W.a₄ * xd + W.a₆) := by
    linear_combination eqd - xd * yd * h1 - yd * h3 + xd ^ 2 * h2
  have hr : ‖W.a₄ * xd + W.a₆‖ ≤ ‖xd‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) h4
    · linarith
  have hX2 : 1 < ‖xd‖ ^ 2 := by nlinarith
  have hX3 : ‖xd‖ < ‖xd‖ ^ 3 := by
    have hm := mul_lt_mul_of_pos_left hX2 hX0
    nlinarith
  have hne2 : ‖xd ^ 3‖ ≠ ‖W.a₄ * xd + W.a₆‖ := by
    rw [norm_pow]
    exact ne_of_gt (lt_of_le_of_lt hr hX3)
  have hY : ‖yd‖ ^ 2 = ‖xd‖ ^ 3 := by
    rw [← norm_pow, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne2, norm_pow,
      max_eq_left (by linarith)]
  have hYpos : 0 < ‖yd‖ := by
    by_contra hneg
    have h0 : ‖yd‖ = 0 := le_antisymm (not_lt.1 hneg) (norm_nonneg _)
    rw [h0] at hY
    have := pow_pos hX0 3
    nlinarith
  have hne1 : ‖px W (A + B)‖ ≠ ‖-xd‖ := ne_of_lt (by rw [norm_neg]; linarith)
  have hxs : ‖px W (A + B) - xd‖ = ‖xd‖ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne1, norm_neg,
      max_eq_right (by linarith)]
  have h2n : ‖(2 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (1 : C) 1
    rw [one_add_one_eq_two, norm_one, max_self] at h
    exact h
  have h4n : ‖(4 : C)‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (2 : C) 2
    rw [show (2 : C) + 2 = 4 by norm_num] at h
    exact h.trans (max_le h2n h2n)
  have hn := congrArg norm hc'
  rw [norm_mul, norm_pow, hxs, norm_mul, norm_mul, norm_neg] at hn
  have ha0 := norm_nonneg (py W A)
  have hb0 := norm_nonneg (py W B)
  have h40 := norm_nonneg (4 : C)
  have hab : ‖(4 : C)‖ * ‖py W A‖ ≤ 1 := by nlinarith
  have habc : ‖(4 : C)‖ * ‖py W A‖ * ‖py W B‖ ≤ 1 := by nlinarith [mul_nonneg h40 ha0]
  have hbound : ‖px W A - px W B‖ ^ 2 * ‖xd‖ ≤ 1 := by rw [hn]; exact habc
  show ‖px W A - px W B‖ ≤ ‖-xd / yd‖
  rw [norm_div, norm_neg]
  have hq : (‖xd‖ / ‖yd‖) ^ 2 * ‖xd‖ = 1 := by
    rw [div_pow, hY]
    first
      | (field_simp; ring)
      | field_simp
  have hs0 := norm_nonneg (px W A - px W B)
  have hq0 : 0 ≤ ‖xd‖ / ‖yd‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  by_contra hlt
  push_neg at hlt
  have hsq : (‖xd‖ / ‖yd‖) ^ 2 < ‖px W A - px W B‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.2 hlt) (by linarith : 0 < ‖px W A - px W B‖ + ‖xd‖ / ‖yd‖)]
  nlinarith
end ReciprocityTheory.ChartRestriction.L1
