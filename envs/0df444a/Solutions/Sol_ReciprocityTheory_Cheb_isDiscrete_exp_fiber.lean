-- Prove2me | solution 1 for ReciprocityTheory.Cheb.isDiscrete_exp_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:54.662009+00:00
-- url     : https://prove2.me/submissions/a7ea3e3a-347b-4943-acac-182717c4b098

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Cheb
open Filter Topology Set Complex
namespace ReciprocityTheory.Cheb
theorem _root_.solution (c : ℂ) : IsDiscrete {w : ℂ | Complex.exp w = c} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y 1, Metric.isOpen_ball, ?_⟩
  ext w
  simp only [mem_inter_iff, Metric.mem_ball, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hwc⟩
    have hexp : Complex.exp w = Complex.exp y := hwc.trans hy.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      simpa using hn
    have hd : dist w y = |(n : ℝ)| * (2 * Real.pi) := by
      rw [dist_eq_norm, hn, add_sub_cancel_left, norm_mul, Complex.norm_intCast]
      simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have := Real.pi_gt_three
    nlinarith
  · rintro rfl
    exact ⟨Metric.mem_ball_self one_pos, hy⟩
end ReciprocityTheory.Cheb
