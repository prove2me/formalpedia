-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_real_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:48.724623+00:00
-- url     : https://prove2.me/submissions/450ed723-b10e-4173-837d-ddb40564f81f

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix
private theorem two_mul_one_add_mul_le_of_le_mul (a b c d s : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hcd : c ≤ s * d) (hs1 : s < 1) (hle : a * c ≤ b * d) :
    2 * (1 + s) * (a * c) ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
  rcases eq_or_lt_of_le hd with h0 | hdpos
  · subst h0
    have hc0 : c = 0 := le_antisymm (by simpa using hcd) hc
    subst hc0
    nlinarith [mul_nonneg hs (sq_nonneg a), sq_nonneg b]
  · have hsq : (a * c) * (a * c) ≤ (b * d) * (b * d) :=
      mul_self_le_mul_self (mul_nonneg ha hc) hle
    have hdc : 0 ≤ d - c := by nlinarith
    have hsdc : 0 ≤ s * d - c := by linarith
    have e1 : 0 ≤ (s * d ^ 2 + c ^ 2) * (a - d) ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg hs (sq_nonneg d)) (sq_nonneg c)) (sq_nonneg _)
    have e2 : 0 ≤ 2 * a * d * ((d - c) * (s * d - c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha) hd) (mul_nonneg hdc hsdc)
    have hd2 : 0 < d ^ 2 := pow_pos hdpos 2
    by_contra hneg
    push_neg at hneg
    have e3 := mul_lt_mul_of_pos_left hneg hd2
    nlinarith
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (a b c d s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hs1 : s < 1) (hba : b ≤ s * a) (hcd : c ≤ s * d) (h1 : |t| ≤ a * c)
    (h2 : |t| ≤ b * d) :
    0 ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 + 2 * (1 + s) * t ∧
      0 ≤ s * (a ^ 2 + d ^ 2) - (b ^ 2 + c ^ 2) - 2 * (1 - s) * t := by
  have hTc : |t| ≤ a * c := h1
  have hTad : |t| ≤ s * a * d := by
    have := mul_le_mul_of_nonneg_left hcd ha
    nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith
  have key : 2 * (1 + s) * |t| ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
    rcases le_total (a * c) (b * d) with hle | hle
    · have e := two_mul_one_add_mul_le_of_le_mul a b c d s ha hc hd hs hcd hs1 hle
      have e' := mul_le_mul_of_nonneg_left hTc (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
    · have e := two_mul_one_add_mul_le_of_le_mul d c b a s hd hb ha hs hba hs1
        (by rw [mul_comm d b, mul_comm c a]; exact hle)
      have e' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
  have htl : 0 ≤ t + |t| := by linarith [neg_abs_le t]
  have htu : t ≤ |t| := le_abs_self t
  have hb2 : b * b ≤ (s * a) * (s * a) := mul_self_le_mul_self hb hba
  have hc2 : c * c ≤ (s * d) * (s * d) := mul_self_le_mul_self hc hcd
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)) htl]
  · nlinarith [mul_nonneg (mul_nonneg hs hs0) (sq_nonneg (a - d)),
      mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s * a * d - t)]
end ReciprocityTheory.MultiplicativeHeights
