-- Prove2me | solution 1 for PI.VolStabW.VolAAW.eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:17.366364+00:00
-- url     : https://prove2.me/submissions/aa1e66cd-6fc6-445c-994a-d17be0b8ff0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
namespace PI.VolStabW.VolAAW
theorem _root_.solution (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  have hsq : ∀ w : ℂ, ‖w‖ = 1 → w.re ^ 2 + w.im ^ 2 = 1 := by
    intro w hw
    have h1 := Complex.sq_norm w
    rw [hw, Complex.normSq_apply] at h1
    nlinarith
  have hre : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
    intro w hw
    have := hsq w hw
    rw [sq, Complex.mul_re]
    nlinarith
  have hn : ∀ k : ℕ, ‖z ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hz, one_pow]
  have hle : ∀ k : ℕ, (z ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hn k).le
  have key : ∀ k : ℕ, (3 : ℝ) ^ k * (1 - z.re) ≤ 1 - (z ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, hre _ (hn k)]
      have h1 := h k
      have h2 := hle k
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℝ) ≤ 2 * (z ^ 2 ^ k).re - 1)]
  have hz1 : z.re ≤ 1 := by simpa using hle 0
  have hre1 : z.re = 1 := by
    by_contra hne
    have hε : 0 < 1 - z.re := by
      rcases lt_or_eq_of_le hz1 with h' | h'
      · linarith
      · exact absurd h' hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - z.re)) (by norm_num : (1 : ℝ) < 3)
    have h1 := key k
    have h2 := h k
    have h3 : 1 < (3 : ℝ) ^ k * (1 - z.re) := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    linarith
  have him : z.im = 0 := by
    have := hsq z hz
    rw [hre1] at this
    nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])
end PI.VolStabW.VolAAW
