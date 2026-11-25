-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:44.66749+00:00
-- url     : https://prove2.me/submissions/ea070b14-a3cb-4fc0-8426-9802d1df9a72

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2
open Complex Real
namespace PositivityTheory.RgUd.T2
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ 1 / 2) : z = 1 := by

  have hup : ∀ n : ℕ, ‖z‖ ^ n ≤ 3 / 2 := fun n => by
    have h1 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_le_norm_sub_add (z ^ n) 1
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hlo : ∀ n : ℕ, 1 / 2 ≤ ‖z‖ ^ n := fun n => by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖z ^ n‖ + ‖z ^ n - 1‖ := by
      simpa [norm_sub_rev] using norm_le_insert' (1 : ℂ) (z ^ n)
    rw [norm_pow] at h1
    have := h n
    simp at h1
    linarith
  have hz1 : ‖z‖ = 1 := by
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hlt
      linarith [hlo n]
    · exact heq
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) hgt
      linarith [hup n]
  have hmem : z ∈ Submonoid.unitSphere ℂ := by
    simpa [Submonoid.unitSphere] using hz1
  let w : Circle := (⟨z, hmem⟩ : Submonoid.unitSphere ℂ)
  have hw : (w : ℂ) = z := rfl
  have hw1 : w = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    rw [Circle.mem_centeredArc (by linarith [pi_pos]), Circle.coe_pow, hw]
    refine abs_arg_lt_pi_div_two_iff.2 (Or.inl ?_)
    have h2 := abs_re_le_norm (z ^ n - 1)
    have h3 := h n
    rw [sub_re, one_re] at h2
    have h4 := neg_abs_le ((z ^ n).re - 1)
    linarith
  rw [← hw, hw1, Circle.coe_one]
end PositivityTheory.RgUd.T2
