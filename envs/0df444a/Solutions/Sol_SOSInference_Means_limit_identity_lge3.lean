-- Prove2me | solution 1 for SOSInference.Means.limit_identity_lge3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:57:16.278597+00:00
-- url     : https://prove2.me/submissions/e4a10d03-60bc-49c7-bdd7-df78427a4e9c

import Mathlib
import Definitions.Def_SOSInference_Means_sos

open SOSInference.Means
open scoped RealInnerProductSpace

theorem solution {l : ℕ} (hl : 3 ≤ l) (C : ℝ) (hC : 0 < C) (z : E l) :
    IsGreatest
      (Set.range fun ζ : E l => -2 * ⟪ζ, z⟫ - 2 * C / ((l : ℝ) + 2) * ‖ζ‖ ^ (l + 2))
      ((2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * ‖z‖ ^ (1 + 1 / ((l : ℝ) + 1)) /
        C ^ (1 / ((l : ℝ) + 1))) ∧
    ∀ ζstar : E l, ζstar = -(‖z‖ ^ (1 / ((l : ℝ) + 1) - 1) / C ^ (1 / ((l : ℝ) + 1))) • z →
      -2 * ⟪ζstar, z⟫ - 2 * C / ((l : ℝ) + 2) * ‖ζstar‖ ^ (l + 2) =
        (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * ‖z‖ ^ (1 + 1 / ((l : ℝ) + 1)) /
          C ^ (1 / ((l : ℝ) + 1)) := by
  set s : ℝ := 1 / ((l : ℝ) + 1) with hs
  have hL1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
  have hL2 : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  have hs0 : 0 < s := by positivity
  have hCs : 0 < C ^ s := Real.rpow_pos_of_pos hC s
  by_cases hz : z = 0
  · subst hz
    have h0 : ‖(0 : E l)‖ ^ (1 + s) = 0 := by
      rw [norm_zero]; exact Real.zero_rpow (by positivity)
    rw [h0]
    refine ⟨⟨⟨0, by simp⟩, ?_⟩, ?_⟩
    · rintro v ⟨ζ, rfl⟩
      simp only [inner_zero_right, mul_zero, zero_mul, zero_div]
      have : 0 ≤ 2 * C / ((l : ℝ) + 2) * ‖ζ‖ ^ (l + 2) := by positivity
      linarith
    · intro ζ hζ
      subst hζ
      simp
  · have nz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set N := ‖z‖ with hN
    set r : ℝ := N ^ s / C ^ s with hr
    have hr0 : 0 < r := div_pos (Real.rpow_pos_of_pos nz s) hCs
    have hrpow : r ^ (l + 1) = N / C := by
      rw [hr, ← Real.div_rpow nz.le hC.le, ← Real.rpow_mul_natCast (div_pos nz hC).le]
      have : s * ((l + 1 : ℕ) : ℝ) = 1 := by
        rw [hs]; push_cast; field_simp
      rw [this, Real.rpow_one]
    have hNs : N ^ (1 + s) = N * N ^ s := by
      rw [Real.rpow_add nz, Real.rpow_one]
    have hV : (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * N ^ (1 + s) / C ^ s =
        (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * N * r := by
      rw [hNs, hr]; ring
    have hrl2 : 2 * C / ((l : ℝ) + 2) * r ^ (l + 2) = 2 * N * r / ((l : ℝ) + 2) := by
      rw [show l + 2 = (l + 1) + 1 by ring, pow_succ, hrpow]
      field_simp
    have key : 2 * N * r - 2 * C / ((l : ℝ) + 2) * r ^ (l + 2) =
        (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * N * r := by
      rw [hrl2]; field_simp; ring
    rw [hV]
    -- value at ζstar
    have hstar : ∀ ζstar : E l, ζstar = -(N ^ (s - 1) / C ^ s) • z →
        -2 * ⟪ζstar, z⟫ - 2 * C / ((l : ℝ) + 2) * ‖ζstar‖ ^ (l + 2) =
          (2 * (l : ℝ) + 2) / ((l : ℝ) + 2) * N * r := by
      intro ζstar hζ
      have hc : N ^ (s - 1) / C ^ s * N = r := by
        rw [Real.rpow_sub_one nz.ne', hr]; field_simp
      have hcpos : 0 ≤ N ^ (s - 1) / C ^ s := by positivity
      have hnorm : ‖ζstar‖ = r := by
        rw [hζ, norm_smul, norm_neg, Real.norm_of_nonneg hcpos, ← hN, hc]
      have hinner : ⟪ζstar, z⟫ = -(N * r) := by
        rw [hζ, inner_smul_left, real_inner_self_eq_norm_sq, ← hN]
        simp only [conj_trivial]
        rw [← hc]; ring
      rw [hnorm, hinner, ← key]; ring
    refine ⟨⟨⟨_, hstar _ rfl⟩, ?_⟩, hstar⟩
    rintro v ⟨ζ, rfl⟩
    dsimp only
    set t := ‖ζ‖ with ht
    have ht0 : 0 ≤ t := norm_nonneg _
    have hin : -2 * ⟪ζ, z⟫ ≤ 2 * t * N := by
      have := abs_real_inner_le_norm ζ z
      have := neg_abs_le ⟪ζ, z⟫
      nlinarith
    -- Bernoulli
    have hb : r ^ (l + 2) + ((l + 2 : ℕ) : ℝ) * r ^ (l + 1) * (t - r) ≤ t ^ (l + 2) := by
      have h1 := one_add_mul_le_pow (a := (t - r) / r)
        (by rw [le_div_iff₀ hr0]; nlinarith) (l + 2)
      have h2 : (1 + (t - r) / r) = t / r := by field_simp; ring
      rw [h2, div_pow] at h1
      rw [le_div_iff₀ (pow_pos hr0 _)] at h1
      have h3 : (1 + ((l + 2 : ℕ) : ℝ) * ((t - r) / r)) * r ^ (l + 2) =
          r ^ (l + 2) + ((l + 2 : ℕ) : ℝ) * r ^ (l + 1) * (t - r) := by
        rw [show l + 2 = (l + 1) + 1 by ring, pow_succ]; field_simp
      linarith
    rw [hrpow] at hb
    have ha : 0 ≤ 2 * C / ((l : ℝ) + 2) := by positivity
    have hb' := mul_le_mul_of_nonneg_left hb ha
    have h4 : 2 * C / ((l : ℝ) + 2) * (((l + 2 : ℕ) : ℝ) * (N / C) * (t - r)) =
        2 * N * (t - r) := by
      push_cast; field_simp
    rw [mul_add, h4] at hb'
    rw [← key]
    linarith
