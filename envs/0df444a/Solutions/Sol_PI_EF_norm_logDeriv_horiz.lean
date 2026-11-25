-- Prove2me | solution 1 for PI.EF.norm_logDeriv_horiz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:15.374135+00:00
-- url     : https://prove2.me/submissions/30ffdf25-ee30-4972-bc12-1f7836b29e38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
import Theorems.Thm_PI_EF_norm_logDeriv_le
import Theorems.Thm_PI_EF_log_two_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T' : ℝ} (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) (him : |s.im| = T') :
    ‖logDeriv (LFunction χ) s‖ ≤ (4 * Cl + 2 * Cw * κ + 16) * Real.log (N * T') ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓ2 : Real.log 2 ≤ Real.log (N * T') := log_two_le_log hT'
  have hl2 := Real.log_two_gt_d9
  have hlogT2 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * T') := by
    have e : 2 * Real.log (N * T') = Real.log ((N * T') ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    apply Real.log_le_log (by nlinarith)
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : T' + 2 ≤ T' ^ 2 := by nlinarith
    calc (N : ℝ) * (T' + 2) ≤ N * T' ^ 2 := mul_le_mul_of_nonneg_left hT2 (by linarith)
      _ ≤ N ^ 2 * T' ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = (N * T') ^ 2 := by ring
  have hlogpos2 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  unfold PI.EF.GoodHeight at hg
  set ℓ := Real.log (N * T') with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hd : 0 < 1 / (κ * ℓ) := one_div_pos.mpr (mul_pos hκ hℓpos)
  have hsim : 2 ≤ |s.im| := by rw [him]; exact hT'
  have hs0 : 1 / 2 ≤ ‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hsim
  have hL0 : LFunction χ s ≠ 0 := by
    intro h0
    rcases hZ N χ hχ s (by linarith) hs1' h0 with ⟨a1, a2⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · have := hg s a1 a2 h0
      rw [him, sub_self, abs_zero] at this
      linarith
    · rw [a] at hsim
      norm_num at hsim
    · rw [a] at hsim
      norm_num at hsim
  have hnear : ∀ ρ ∈ ZerosNear χ s.im, 1 / (κ * ℓ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, a4⟩ := hρ
    have hgρ := hg ρ a1 a2 a4
    have k1 : |(|ρ.im|) - T'| ≤ |s.im - ρ.im| := by
      rw [← him, abs_sub_comm]
      exact abs_abs_sub_abs_le_abs_sub s.im ρ.im
    have k2 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    linarith
  have key := norm_logDeriv_le hW hL χ hχ s h1 h2 hL0 hs0 hs1 hd hnear
  rw [him, div_div_eq_mul_div, div_one] at key
  refine le_trans key ?_
  have h_a : Cl * Real.log (N * (T' + 2)) ≤ Cl * (2 * ℓ) := mul_le_mul_of_nonneg_left hlogT2 hCl
  have h_b : 2 * ℓ ≤ 4 * ℓ ^ 2 := by nlinarith
  have h_c : Cl * (2 * ℓ) ≤ Cl * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h_b hCl
  have h_d : Cw * Real.log (N * (T' + 2)) * (κ * ℓ) ≤ Cw * (2 * ℓ) * (κ * ℓ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2 hCw) (mul_pos hκ hℓpos).le
  have h_e : 4 ≤ 16 * ℓ ^ 2 := by nlinarith
  nlinarith [h_a, h_c, h_d, h_e]
end PI.EF
