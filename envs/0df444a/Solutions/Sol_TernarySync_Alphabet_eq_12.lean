-- Prove2me | solution 1 for TernarySync.Alphabet.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:21:01.388567+00:00
-- url     : https://prove2.me/submissions/d6ee6635-3a36-4966-b94e-03d57e4b6d2b

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource
import Theorems.Thm_TernarySync_Alphabet_eq_11

section
set_option autoImplicit false

namespace TernarySync.Dev.Eq12
open TernarySync.Alphabet

theorem choose_le_exp (ℓ d : ℕ) (hd : 1 ≤ d) :
    (ℓ.choose d : ℝ) ≤ Real.exp (d * (1 + Real.log ℓ - Real.log d)) := by
  have h1 : (ℓ.choose d : ℝ) ≤ (ℓ : ℝ) ^ d / (d.factorial : ℝ) := Nat.choose_le_pow_div d ℓ
  have h2 := Real.pow_div_factorial_le_exp (d : ℝ) (Nat.cast_nonneg d) d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have h3 : (d : ℝ) ^ d ≤ Real.exp d * d.factorial := by
    rw [div_le_iff₀ hf] at h2; exact h2
  rcases Nat.eq_zero_or_pos ℓ with hl | hl
  · subst hl
    have : (Nat.choose 0 d : ℝ) = 0 := by simp [Nat.choose_eq_zero_of_lt hd]
    rw [this]; exact (Real.exp_pos _).le
  have hlpos : (0 : ℝ) < ℓ := by exact_mod_cast hl
  refine h1.trans ?_
  have e : Real.exp (d * (1 + Real.log ℓ - Real.log d)) = Real.exp d * (ℓ : ℝ) ^ d / (d : ℝ) ^ d := by
    rw [show (d : ℝ) * (1 + Real.log ℓ - Real.log d) = d + d * Real.log ℓ - d * Real.log d by ring,
      Real.exp_sub, Real.exp_add, ← Real.rpow_natCast, ← Real.rpow_natCast,
      Real.rpow_def_of_pos hlpos, Real.rpow_def_of_pos hdpos]
    ring_nf
  rw [e, div_le_div_iff₀ hf (by positivity)]
  nlinarith [pow_pos hlpos d, h3]

theorem phi_mono (ℓ : ℝ) (hℓ : 0 < ℓ) :
    MonotoneOn (fun x : ℝ => x * (2 + 2 * Real.log ℓ + Real.log 3 - 2 * Real.log x))
      (Set.Ioc 0 ℓ) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt
      (fun x : ℝ => x * (2 + 2 * Real.log ℓ + Real.log 3 - 2 * Real.log x))
      (1 * (2 + 2 * Real.log ℓ + Real.log 3 - 2 * Real.log x) +
        x * (0 - 2 * x⁻¹)) x := by
    intro x hx
    exact (hasDerivAt_id x).mul ((hasDerivAt_const x _).sub
      ((Real.hasDerivAt_log hx.ne').const_mul 2))
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 ℓ)
  · intro x hx
    exact (hd x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hd x hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    rw [(hd x hx.1).deriv]
    have hxne : x ≠ 0 := hx.1.ne'
    have : x * (0 - 2 * x⁻¹) = -2 := by field_simp; ring
    rw [this]
    have hlog : Real.log x ≤ Real.log ℓ := Real.log_le_log hx.1 hx.2.le
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith

theorem num_bound : Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3 < 18 := by
  have h2 : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : Real.log 3 < 1.2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
    have h02 : (1.2 : ℝ) ≤ Real.exp 0.2 := by
      have := Real.add_one_le_exp (0.2 : ℝ); linarith
    rw [this]; nlinarith
  have h1000 : Real.log 1000 < 7 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
      apply pow_le_pow_left₀ (by norm_num); linarith
    norm_num at h27 ⊢
    linarith
  have : Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) = 1 + Real.log 1000 := by
    rw [show Real.exp 1 / ((1 : ℝ) / 1000) = Real.exp 1 * 1000 by field_simp,
      Real.log_mul (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]
  rw [this]
  linarith

end TernarySync.Dev.Eq12

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq12 in
theorem chk_eq_12 (ℓ : ℕ) (hℓ : 1 < (1 : ℝ) / 1000 * (ℓ : ℝ)) (y : List (Fin 3))
    (hy : y.length = ℓ) :
    ((delBall ((1 : ℝ) / 1000) ℓ y).ncard : ℝ) ≤
        Real.exp ((1 : ℝ) / 1000 * (ℓ : ℝ) *
          (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3)) ∧
      Real.exp ((1 : ℝ) / 1000 * (ℓ : ℝ) *
          (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3)) <
        Real.exp (9 * (ℓ : ℝ) / 500) := by
  set m : ℝ := (1 : ℝ) / 1000 * (ℓ : ℝ) with hm
  have hℓ1000 : 1000 < ℓ := by
    have : (1000 : ℝ) < ℓ := by rw [hm] at hℓ; linarith
    exact_mod_cast this
  have hlpos : (0 : ℝ) < ℓ := by positivity
  have hmpos : 0 < m := by linarith
  have hmℓ : m ≤ ℓ := by rw [hm]; linarith
  have hnum := num_bound
  refine ⟨?_, ?_⟩
  swap
  · apply Real.exp_lt_exp.mpr
    rw [show 9 * (ℓ : ℝ) / 500 = m * 18 by rw [hm]; ring]
    exact mul_lt_mul_of_pos_left hnum hmpos
  have h11 := eq_11 (β := Fin 3) ℓ hℓ1000 y hy
  refine h11.trans ?_
  simp only [Fintype.card_fin]
  set a : ℝ := 2 + 2 * Real.log ℓ + Real.log 3 with ha
  set φ : ℝ → ℝ := fun x => x * (a - 2 * Real.log x) with hφ
  have hlogm : Real.log ℓ = Real.log m + Real.log 1000 := by
    rw [← Real.log_mul hmpos.ne' (by norm_num)]
    congr 1; rw [hm]; ring
  have hφm : φ m = m * (2 + 2 * Real.log 1000 + Real.log 3) := by
    simp only [hφ, ha, hlogm]; ring
  have hφm0 : 0 ≤ φ m := by
    rw [hφm]
    have : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num)
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  have hterm : ∀ d ∈ (Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < m),
      ((ℓ.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d) ≤ Real.exp (φ m) := by
    intro d hd
    have hdm : (d : ℝ) < m := (Finset.mem_filter.mp hd).2
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0; simpa using Real.one_le_exp hφm0
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hpos
    have hc := choose_le_exp ℓ d hpos
    have hc0 : (0 : ℝ) ≤ ℓ.choose d := Nat.cast_nonneg _
    have h3 : (3 : ℝ) ^ d = Real.exp (d * Real.log 3) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hsq : ((ℓ.choose d : ℝ)) ^ 2 ≤ Real.exp (d * (1 + Real.log ℓ - Real.log d)) ^ 2 := by
      gcongr
    calc ((ℓ.choose d : ℝ) ^ 2 * (3 : ℝ) ^ d)
        ≤ Real.exp (d * (1 + Real.log ℓ - Real.log d)) ^ 2 * Real.exp (d * Real.log 3) := by
          rw [h3]; gcongr
      _ = Real.exp (φ d) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1
          simp only [hφ, ha]; push_cast; ring
      _ ≤ Real.exp (φ m) := by
          apply Real.exp_le_exp.mpr
          exact phi_mono (ℓ : ℝ) hlpos ⟨hdpos, hdm.le.trans hmℓ⟩ ⟨hmpos, hmℓ⟩ hdm.le
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [nsmul_eq_mul]
  have hcard : (((Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < m)).card : ℝ) ≤ 2 ^ m := by
    have hsub : (Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < m) ⊆
        Finset.range (⌊m⌋₊ + 1) := by
      intro d hd
      have := (Finset.mem_filter.mp hd).2
      rw [Finset.mem_range]
      have := Nat.le_floor this.le
      omega
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 : ((⌊m⌋₊ + 1 : ℕ) : ℝ) ≤ m + 1 := by
      push_cast; linarith [Nat.floor_le hmpos.le]
    have h3 : 1 + m * 1 ≤ ((1 : ℝ) + 1) ^ m :=
      one_add_mul_self_le_rpow_one_add (s := 1) (p := m) (by norm_num) (by linarith)
    have : (((Finset.range (ℓ + 1)).filter (fun d : ℕ => (d : ℝ) < m)).card : ℝ) ≤ m + 1 :=
      le_trans (by exact_mod_cast h1) h2
    norm_num at h3
    linarith
  calc _ ≤ (2 : ℝ) ^ m * Real.exp (φ m) := by gcongr
    _ = Real.exp (m * (Real.log 2 + 2 * Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) + Real.log 3)) := by
        rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, hφm]
        have : Real.log (Real.exp 1 / ((1 : ℝ) / 1000)) = 1 + Real.log 1000 := by
          rw [show Real.exp 1 / ((1 : ℝ) / 1000) = Real.exp 1 * 1000 by field_simp,
            Real.log_mul (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]
        rw [this]; congr 1; ring
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_12 := @TernarySync.Alphabet.chk_eq_12
