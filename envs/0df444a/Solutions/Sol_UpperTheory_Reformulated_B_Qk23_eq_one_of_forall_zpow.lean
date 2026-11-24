-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:57.569278+00:00
-- url     : https://prove2.me/submissions/05cd3d68-83f5-416b-b5bd-b82f6700a635

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfForallZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Qk23.half_le_re {w : ℂ} (h : ‖w⁻¹ - 1‖ < 1) : (1 / 2 : ℝ) ≤ w.re := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at h
  have e : w⁻¹ - 1 = (1 - w) / w := by field_simp
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hw)] at h
  have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by
    have := norm_nonneg (1 - w)
    nlinarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk23
theorem _root_.solution :
    ∀ {z : ℂ}, (∀ (k : ℤ), ‖z ^ k - (1 : ℂ)‖ < (1 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re := by
    intro k
    apply UpperTheory.Reformulated.B.Qk23.half_le_re
    have := h (-(k : ℤ))
    rwa [zpow_neg, zpow_natCast] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  rw [div_lt_iff₀ hd] at hn
  have h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ)
      (fun k _ => hre k)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1 := by
    rw [← norm_mul, geom_sum_mul]
    have := h (n : ℤ)
    rwa [zpow_natCast] at this
  have h3 := mul_le_mul_of_nonneg_right h1 hd.le
  linarith
end UpperTheory.Reformulated.B.Qk23
