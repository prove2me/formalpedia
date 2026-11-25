-- Prove2me | solution 1 for PI.DefPosDefWork.conj_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:35:10.89454+00:00
-- url     : https://prove2.me/submissions/4a62b8e4-5ecb-416b-90d5-dfdb1833b870

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_SplittingOfExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder
namespace PI.DefPosDefWork
theorem _root_.solution (w z : ℂ)
    (h : ∀ q : ℚ, z + (q : ℂ) ≠ 0 → ∃ c : ℝ, 0 < c ∧ (w + (q : ℂ)) * (z + (q : ℂ)) = (c : ℂ)) :
    w = (starRingEnd ℂ) z := by
  have key : ∀ q : ℚ, z + (q : ℂ) ≠ 0 →
      (w.re + q) * z.im + w.im * (z.re + q) = 0 ∧ 0 < (w.re + q) * (z.re + q) - w.im * z.im := by
    intro q hq
    obtain ⟨c, hc, he⟩ := h q hq
    have him := congrArg Complex.im he
    have hre := congrArg Complex.re he
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im, add_zero] at him hre
    constructor
    · linear_combination him
    · have hc' : (w.re + q) * (z.re + q) - w.im * z.im = c := by linear_combination hre
      rw [hc']
      exact hc
  rw [Complex.ext_iff, Complex.conj_re, Complex.conj_im]
  by_cases hd : z.im = 0
  · have hne : ∀ q : ℚ, z.re + q ≠ 0 → z + (q : ℂ) ≠ 0 := fun q hq h0 =>
      hq (by simpa using congrArg Complex.re h0)
    obtain ⟨q0, hq0⟩ : ∃ q : ℚ, z.re + q ≠ 0 := by
      by_cases h0 : z.re = 0
      · exact ⟨1, by rw [h0]; norm_num⟩
      · exact ⟨0, by simpa using h0⟩
    have k := key q0 (hne q0 hq0)
    have e4 : w.im * (z.re + q0) = 0 := by linear_combination k.1 - (w.re + (q0 : ℝ)) * hd
    have him : w.im = 0 := (mul_eq_zero.mp e4).resolve_right hq0
    have ere : w.re = z.re := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : w.re + q < 0 := by linarith
        have hB : 0 < z.re + q := by linarith
        have k2 := (key q (hne q hB.ne')).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_neg_of_pos hA hB]
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (neg_lt_neg hlt)
        have hA : 0 < w.re + q := by linarith
        have hB : z.re + q < 0 := by linarith
        have k2 := (key q (hne q hB.ne)).2
        rw [him, zero_mul, sub_zero] at k2
        linarith [mul_neg_of_pos_of_neg hA hB]
    exact ⟨ere, by rw [him, hd, neg_zero]⟩
  · have hne : ∀ q : ℚ, z + (q : ℂ) ≠ 0 := fun q h0 => hd (by simpa using congrArg Complex.im h0)
    have k0 := key 0 (hne 0)
    have k1 := key 1 (hne 1)
    push_cast at k0 k1
    have e1 : w.im = -z.im := by linear_combination k1.1 - k0.1
    have e2 : z.im * (w.re - z.re) = 0 := by linear_combination k0.1 - z.re * e1
    have e3 : w.re = z.re := by
      rcases mul_eq_zero.mp e2 with h0 | h0
      · exact absurd h0 hd
      · linarith
    exact ⟨e3, e1⟩
end PI.DefPosDefWork
