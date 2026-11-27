-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_main_4813835306a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:41.835532+00:00
-- url     : https://prove2.me/submissions/6d86a447-4da6-4ef4-bc64-3ff67c187183

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivBoundLeftHalfPlane
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__ExplChiLeft_bound_right_960b4eaa5826
import Theorems.Thm_GlobalTheory_LFunction_zero_of_re_nonpos
import Theorems.Thm_GlobalTheory_T_digamma_log_bound_left_region
import Theorems.Thm_GlobalTheory_T_digamma_log_bound_right_half_plane
import Theorems.Thm_GlobalTheory_T_dirichlet_logDeriv_reflection_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
namespace GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N →
    χ.IsPrimitive → ∀ s : ℂ, s.re ≤ -(1/2 : ℝ) →
    (1 ≤ |s.im| ∨ ∃ k : ℕ, s.re = -((k : ℝ) + 1/2)) →
    DirichletCharacter.LFunction χ s ≠ 0 ∧
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ C * Real.log (N * (‖s‖ + 2)) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.T.digamma_log_bound_right_half_plane
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.digamma_log_bound_left_region
  obtain ⟨B, hB, HB⟩ := bound_right
  refine ⟨4 + C₁ + C₂ + B, by positivity, ?_⟩
  intro N _ χ hN hχ s hre hs

  have hint : ∀ m : ℤ, s ≠ (m : ℂ) := by
    rintro m rfl
    rcases hs with h | ⟨k, hk⟩
    · simp at h
      linarith
    · have hk' : (m : ℝ) = -((k : ℝ) + 1 / 2) := by simpa using hk
      have h2 : ((2 * m + 2 * k + 1 : ℤ) : ℝ) = 0 := by
        push_cast
        linarith
      have h3 : (2 * m + 2 * k + 1 : ℤ) = 0 := by exact_mod_cast h2
      omega
  have hL : LFunction χ s ≠ 0 := by
    intro h0
    obtain ⟨⟨n, hn⟩, -⟩ := GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ s (by linarith) h0
    exact hint (-(n : ℤ)) (by rw [hn]; push_cast; rfl)
  refine ⟨hL, ?_⟩
  have hre' : (3 / 2 : ℝ) ≤ (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have hL' : LFunction χ⁻¹ (1 - s) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inr fun h => by rw [h] at hre'; norm_num at hre')
      (by linarith)
  obtain ⟨a, hpar, m, hm, rfl⟩ : ∃ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) ∧
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ a = (m : ℂ) := by
    rcases χ.even_or_odd with h | h
    · exact ⟨0, Or.inl ⟨h, rfl⟩, 0, Or.inl rfl, by simp⟩
    · exact ⟨1, Or.inr ⟨h, rfl⟩, 1, Or.inr rfl, by simp⟩
  have hm0 : (0 : ℝ) ≤ m := by rcases hm with rfl | rfl <;> simp
  have hm1 : (m : ℝ) ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hnorm : ‖(m : ℂ)‖ ≤ 1 := by rcases hm with rfl | rfl <;> simp
  have hz : (1 / 2 : ℝ) ≤ ((1 - s + (m : ℂ)) / 2).re := by
    have : ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 := by simp
    rw [this]
    linarith
  have hwre : ((s + (m : ℂ)) / 2).re = (s.re + m) / 2 := by simp
  have hwim : ((s + (m : ℂ)) / 2).im = s.im / 2 := by simp
  have hc1 : ∀ n : ℕ, (s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    refine hint (-2 * n - m) ?_
    push_cast
    linear_combination 2 * h
  have hc2 : ∀ n : ℕ, (1 - s + (m : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have h1 := congrArg Complex.re h
    rw [show ((1 - s + (m : ℂ)) / 2).re = (1 - s.re + m) / 2 by simp] at h1
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at h1
    linarith
  rw [GlobalTheory.T.dirichlet_logDeriv_reflection_formula N χ hN hχ _ hpar s hc1 hc2 hL hL']

  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsn : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    have h2 := neg_abs_le s.re
    linarith
  have hpos : 0 < (N : ℝ) * (‖s‖ + 2) := by positivity
  set X := Real.log (N * (‖s‖ + 2)) with hX
  have hX1 : 1 ≤ X := by
    rw [hX, Real.le_log_iff_exp_le hpos]
    have := Real.exp_one_lt_d9
    nlinarith
  have hlogN : Real.log N ≤ X := by
    refine Real.log_le_log (by linarith) ?_
    nlinarith [norm_nonneg s]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi3 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  have t1 : ‖(((Real.log (N / Real.pi) : ℝ)) : ℂ)‖ ≤ 4 * X := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      Real.log_div (by linarith) Real.pi_ne_zero, abs_le]
    constructor <;> linarith
  have t2 : ‖digamma ((1 - s + (m : ℂ)) / 2)‖ ≤ C₁ * X := by
    refine (H₁ _ hz).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(1 - s + (m : ℂ)) / 2‖ ≤ (2 + ‖s‖) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le (1 - s) (m : ℂ)
      have h2 := norm_sub_le (1 : ℂ) s
      simp only [norm_one] at h2
      linarith
    nlinarith [norm_nonneg s]
  have t3 : ‖digamma ((s + (m : ℂ)) / 2)‖ ≤ C₂ * X := by
    have hcond : 1 / 2 ≤ |((s + (m : ℂ)) / 2).im| ∨
        ∃ k : ℤ, ((s + (m : ℂ)) / 2).re = (k : ℝ) / 2 + 1 / 4 := by
      rcases hs with h | ⟨k, hk⟩
      · left
        rw [hwim, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        linarith
      · right
        refine ⟨m - k - 1, ?_⟩
        rw [hwre, hk]
        push_cast
        ring
    refine (H₂ _ (by rw [hwre]; linarith) hcond).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂.le
    refine Real.log_le_log (by positivity) ?_
    have : ‖(s + (m : ℂ)) / 2‖ ≤ (‖s‖ + 1) / 2 := by
      rw [norm_div, Complex.norm_ofNat]
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      have h1 := norm_add_le s (m : ℂ)
      linarith
    nlinarith [norm_nonneg s]
  have t4 := HB N χ⁻¹ (1 - s) hre'
  have hh : ∀ x y z u : ℂ, ‖-x - y / 2 - z / 2 - u‖ ≤ ‖x‖ + ‖y‖ / 2 + ‖z‖ / 2 + ‖u‖ := by
    intro x y z u
    have e : -x - y / 2 - z / 2 - u = -x + -(y / 2) + -(z / 2) + -u := by ring
    rw [e]
    refine (norm_add₄_le).trans ?_
    simp [norm_neg, norm_div]
  refine (hh _ _ _ _).trans ?_
  nlinarith
end GlobalTheory.CompanionTheory.Hypotheses₂.ExplChiLeft
