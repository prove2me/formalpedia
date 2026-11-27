-- Prove2me | solution 2 for PositivityTheory.ThKG.Fub.circle_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:50.683871+00:00
-- url     : https://prove2.me/submissions/7b59b209-7dcc-4504-99cd-44a26f5053b6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {z : Circle} (h : ∀ n : ℕ, ‖((z ^ n : Circle) : ℂ) - 1‖ < 1) : z = 1 := by
  by_contra hz
  have h0 : (z : ℂ) - 1 ≠ 0 := fun e => hz (Circle.coe_eq_one.1 (sub_eq_zero.1 e))
  have hre : ∀ n : ℕ, 1 / 2 < ((z : ℂ) ^ n).re := fun n => by
    have h1 := h n
    rw [Circle.coe_pow] at h1
    have h2 : ‖(z : ℂ) ^ n‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
    have h3 := Complex.sq_norm ((z : ℂ) ^ n - 1)
    have h4 := Complex.sq_norm ((z : ℂ) ^ n)
    rw [Complex.normSq_apply] at h3 h4
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
    nlinarith [norm_nonneg ((z : ℂ) ^ n - 1)]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖(z : ℂ) - 1‖)
  have hp : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.2 h0
  have e : (∑ i ∈ Finset.range N, (z : ℂ) ^ i) * (z - 1) = z ^ N - 1 := geom_sum_mul _ _
  have h1 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, (z : ℂ) ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range N) (fun i => ((z : ℂ) ^ i).re) (1 / 2) fun i _ => (hre i).le
    simpa [div_eq_mul_inv] using this
  have h2 : ‖(z : ℂ) ^ N - 1‖ < 1 := by simpa using h N
  rw [← e, norm_mul] at h2
  rw [div_lt_iff₀ hp] at hN
  nlinarith
end PositivityTheory.ThKG.Fub
