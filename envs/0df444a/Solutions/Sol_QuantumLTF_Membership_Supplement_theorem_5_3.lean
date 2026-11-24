-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T08:19:03.657159+00:00
-- url     : https://prove2.me/submissions/06e44c4c-1da0-4803-916e-6855e3262eb1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_goodBasis53
import Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_band_bounds_53
import Theorems.Thm_QuantumLTF_Membership_Supplement_band_circuits_53

set_option autoImplicit false

namespace GroverParallel53

open QAlgorithms QuantumLTF.Membership

/-! ### 1. Real Trigonometric Window, Amplification, Normalization, and Asymptotic Bounds -/

/-- Single-copy Grover success probability lower bound (`≥ 3 / 100`) across the whole range
`s0 ∈ (0, 1 / √2]` and `sin θ ∈ [(7 / 8) * s0, (9 / 8) * s0]`. -/
lemma grover_window_bound {s0 θ : ℝ}
    (hs0_pos : 0 < s0) (_hs0_le : s0 ≤ 1 / Real.sqrt 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hsin_lo : (7 / 8 : ℝ) * s0 ≤ Real.sin θ)
    (hsin_hi : Real.sin θ ≤ (9 / 8 : ℝ) * s0) :
    let t : ℕ := if s0 ≥ 1 / 5 then 0 else Nat.floor (Real.pi / (4 * s0) - 1)
    (3 / 100 : ℝ) ≤ Real.sin ((2 * (t : ℝ) + 1) * θ) ^ 2 := by
  intro t
  by_cases hs : s0 ≥ 1 / 5
  · have ht : t = 0 := if_pos hs
    rw [ht]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]
    have hsin740 : (7 / 40 : ℝ) ≤ Real.sin θ := by linarith
    have hsq : ((7 / 40 : ℝ) ^ 2) ≤ Real.sin θ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hsin740 2
    linarith [show (3 / 100 : ℝ) ≤ (7 / 40 : ℝ) ^ 2 by norm_num]
  · have hs_lt : s0 < 1 / 5 := lt_of_not_ge hs
    have ht : t = Nat.floor (Real.pi / (4 * s0) - 1) := if_neg hs
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpi_ub : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    have harg_nn : 0 ≤ Real.pi / (4 * s0) - 1 := by
      have : (15 / 4 : ℝ) < Real.pi / (4 * s0) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have ht_le : (t : ℝ) ≤ Real.pi / (4 * s0) - 1 := by
      rw [ht]
      exact Nat.floor_le harg_nn
    have ht_gt : Real.pi / (4 * s0) - 2 < (t : ℝ) := by
      rw [ht]
      have hlt := Nat.lt_floor_add_one (Real.pi / (4 * s0) - 1)
      linarith
    have h2t_lo : Real.pi / (2 * s0) - 3 < 2 * (t : ℝ) + 1 := by
      have : Real.pi / (2 * s0) = 2 * (Real.pi / (4 * s0)) := by ring
      linarith
    have h2t_hi : 2 * (t : ℝ) + 1 ≤ Real.pi / (2 * s0) - 1 := by
      have : Real.pi / (2 * s0) = 2 * (Real.pi / (4 * s0)) := by ring
      linarith
    have h2t_hi' : 2 * (t : ℝ) + 1 < Real.pi / (2 * s0) := by linarith
    have hθ_lo : (7 / 8 : ℝ) * s0 ≤ θ := le_trans hsin_lo (Real.sin_le hθ0)
    have hθ_hi : θ ≤ (Real.pi / 2) * ((9 / 8 : ℝ) * s0) := by
      have hj := Real.mul_le_sin hθ0 hθ1
      have hmul : θ ≤ (Real.pi / 2) * Real.sin θ := by
        calc θ = (Real.pi / 2) * ((2 / Real.pi) * θ) := by field_simp
          _ ≤ (Real.pi / 2) * Real.sin θ := mul_le_mul_of_nonneg_left hj (by positivity)
      exact le_trans hmul (mul_le_mul_of_nonneg_left hsin_hi (by positivity))
    have hpi_2s0_ge : (3 : ℝ) ≤ Real.pi / (2 * s0) - 3 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith
    let x : ℝ := (2 * (t : ℝ) + 1) * θ
    have hx_lo : Real.pi / 6 ≤ x := by
      have h1 : (Real.pi / (2 * s0) - 3) * ((7 / 8 : ℝ) * s0) ≤ x :=
        mul_le_mul h2t_lo.le hθ_lo (by positivity) (by linarith)
      have h2 : (Real.pi / (2 * s0) - 3) * ((7 / 8 : ℝ) * s0) =
          7 * Real.pi / 16 - (21 / 8 : ℝ) * s0 := by
        field_simp
        ring
      have h3 : (63 / 80 : ℝ) < 7 * Real.pi / 16 - (21 / 8 : ℝ) * s0 := by nlinarith
      have h4 : Real.pi / 6 < (63 / 80 : ℝ) := by linarith
      linarith
    have hx_hi : x ≤ 9 * Real.pi ^ 2 / 32 := by
      have h1 : x ≤ (Real.pi / (2 * s0)) * ((Real.pi / 2) * ((9 / 8 : ℝ) * s0)) :=
        mul_le_mul h2t_hi'.le hθ_hi hθ0 (by positivity)
      have h2 : (Real.pi / (2 * s0)) * ((Real.pi / 2) * ((9 / 8 : ℝ) * s0)) =
          9 * Real.pi ^ 2 / 32 := by
        field_simp
        ring
      linarith
    have hx_lt_pi : x < Real.pi := by
      have h9pi : 9 * Real.pi / 32 < 1 := by linarith
      have : 9 * Real.pi ^ 2 / 32 = (9 * Real.pi / 32) * Real.pi := by ring
      nlinarith
    by_cases hxhalf : x ≤ Real.pi / 2
    · have hj := Real.mul_le_sin (le_trans (by positivity) hx_lo) hxhalf
      have hsin_lb : (1 / 3 : ℝ) ≤ Real.sin x := by
        have h1 : (2 / Real.pi) * (Real.pi / 6) ≤ (2 / Real.pi) * x :=
          mul_le_mul_of_nonneg_left hx_lo (by positivity)
        have h2 : (2 / Real.pi) * (Real.pi / 6) = 1 / 3 := by field_simp; ring
        linarith
      have hsq : (1 / 3 : ℝ) ^ 2 ≤ Real.sin x ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hsin_lb 2
      linarith [show (3 / 100 : ℝ) ≤ (1 / 3 : ℝ) ^ 2 by norm_num]
    · have hx_gt : Real.pi / 2 < x := lt_of_not_ge hxhalf
      have hu0 : 0 ≤ Real.pi - x := by linarith
      have hu1 : Real.pi - x ≤ Real.pi / 2 := by linarith
      have hsin_eq : Real.sin x = Real.sin (Real.pi - x) := (Real.sin_pi_sub x).symm
      have hj := Real.mul_le_sin hu0 hu1
      have hsin_lb : (1 / 5 : ℝ) ≤ Real.sin x := by
        rw [hsin_eq]
        have h1 : (2 / Real.pi) * (Real.pi - 9 * Real.pi ^ 2 / 32) ≤ (2 / Real.pi) * (Real.pi - x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : (2 / Real.pi) * (Real.pi - 9 * Real.pi ^ 2 / 32) = 2 - 9 * Real.pi / 16 := by
          field_simp
          ring
        have h3 : (1 / 5 : ℝ) ≤ 2 - 9 * Real.pi / 16 := by linarith
        linarith
      have hsq : (1 / 5 : ℝ) ^ 2 ≤ Real.sin x ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hsin_lb 2
      linarith [show (3 / 100 : ℝ) ≤ (1 / 5 : ℝ) ^ 2 by norm_num]

/-- Query count per copy bound: `2 * t + 1 ≤ C_q * K ^ (1 / 4)`. -/
lemma grover_t_bound {K : ℕ} {c_band p1D : ℝ} (hK : 1 ≤ K) (hc : 0 < c_band)
    (hlo : c_band / Real.sqrt K ≤ p1D) (_hhi : p1D ≤ 1) :
    let s0 := Real.sqrt (p1D / 2)
    let t : ℕ := if s0 ≥ 1 / 5 then 0 else Nat.floor (Real.pi / (4 * s0) - 1)
    (2 * (t : ℝ) + 1) ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) := by
  intro s0 t
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hK14_ge1 : (1 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hK1 (by norm_num)
  have hp1D_pos : 0 < p1D := lt_of_lt_of_le (by positivity) hlo
  have hs0_pos : 0 < s0 := Real.sqrt_pos.mpr (by positivity)
  by_cases hs : s0 ≥ 1 / 5
  · have ht : t = 0 := if_pos hs
    rw [ht]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    calc (1 : ℝ) ≤ (K : ℝ) ^ (1 / 4 : ℝ) := hK14_ge1
      _ = 1 * (K : ℝ) ^ (1 / 4 : ℝ) := (one_mul _).symm
      _ ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have ht : t = Nat.floor (Real.pi / (4 * s0) - 1) := if_neg hs
    have hs_lt : s0 < 1 / 5 := lt_of_not_ge hs
    have harg_nn : 0 ≤ Real.pi / (4 * s0) - 1 := by
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have : (15 / 4 : ℝ) < Real.pi / (4 * s0) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have ht_le : (t : ℝ) ≤ Real.pi / (4 * s0) - 1 := by
      rw [ht]
      exact Nat.floor_le harg_nn
    have h2t : 2 * (t : ℝ) + 1 ≤ Real.pi / (2 * s0) := by
      have : Real.pi / (2 * s0) = 2 * (Real.pi / (4 * s0)) := by ring
      linarith
    have hsqrt_K : Real.sqrt (Real.sqrt (K : ℝ)) = (K : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hKpos.le]
      norm_num
    have hs0_lb : Real.sqrt (c_band / 2) / Real.sqrt (Real.sqrt (K : ℝ)) ≤ s0 := by
      have h1 : (c_band / 2) / Real.sqrt (K : ℝ) ≤ p1D / 2 := by
        have : (c_band / 2) / Real.sqrt (K : ℝ) = (c_band / Real.sqrt (K : ℝ)) / 2 := by ring
        linarith
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_div (by positivity)] at h2
      exact h2
    have hinv_s0 : 1 / s0 ≤ Real.sqrt (2 / c_band) * (K : ℝ) ^ (1 / 4 : ℝ) := by
      have hcb_pos : 0 < Real.sqrt (c_band / 2) := Real.sqrt_pos.mpr (by positivity)
      have hsqrt_pos : 0 < Real.sqrt (Real.sqrt (K : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hKpos)
      have hdiv : 1 / s0 ≤ Real.sqrt (Real.sqrt (K : ℝ)) / Real.sqrt (c_band / 2) := by
        rw [div_le_div_iff₀ hs0_pos hcb_pos]
        rw [div_le_iff₀ hsqrt_pos] at hs0_lb
        linarith
      have heq : Real.sqrt (Real.sqrt (K : ℝ)) / Real.sqrt (c_band / 2) =
          Real.sqrt (2 / c_band) * (K : ℝ) ^ (1 / 4 : ℝ) := by
        rw [hsqrt_K, show (2 / c_band : ℝ) = (c_band / 2)⁻¹ by ring, Real.sqrt_inv]
        ring
      linarith
    calc 2 * (t : ℝ) + 1 ≤ Real.pi / (2 * s0) := h2t
      _ = (Real.pi / 2) * (1 / s0) := by ring
      _ ≤ (Real.pi / 2) * (Real.sqrt (2 / c_band) * (K : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv_s0 (by positivity)
      _ = (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) := by ring
      _ ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- `R`-copy parallel amplification failure bound: `(1 - q1)^R ≤ ξ^2 / 16`. -/
lemma amplification_R_prob {q1 ξ : ℝ} (hq1 : 3 / 100 ≤ q1) (hq1_le : q1 ≤ 1)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    let R : ℕ := Nat.ceil (Real.log (16 / ξ ^ 2) / Real.log (100 / 97)) + 2
    (1 - q1) ^ R ≤ ξ ^ 2 / 16 := by
  intro R
  have h1q1_nn : 0 ≤ 1 - q1 := sub_nonneg.mpr hq1_le
  have h1q1_le : 1 - q1 ≤ 97 / 100 := by linarith
  have hpow_mono : (1 - q1) ^ R ≤ (97 / 100 : ℝ) ^ R :=
    pow_le_pow_left₀ h1q1_nn h1q1_le R
  have hlog_pos : 0 < Real.log (100 / 97 : ℝ) := Real.log_pos (by norm_num)
  have h16_gt1 : 1 < 16 / ξ ^ 2 := by
    rw [one_lt_div (by positivity)]
    nlinarith
  have hR_ge : Real.log (16 / ξ ^ 2) / Real.log (100 / 97) ≤ (R : ℝ) := by
    have hc := Nat.le_ceil (Real.log (16 / ξ ^ 2) / Real.log (100 / 97))
    have h2 : (Nat.ceil (Real.log (16 / ξ ^ 2) / Real.log (100 / 97)) : ℝ) ≤ (R : ℝ) := by
      dsimp [R]; push_cast; linarith
    exact le_trans hc h2
  have hmul : Real.log (16 / ξ ^ 2) ≤ (R : ℝ) * Real.log (100 / 97) :=
    (div_le_iff₀ hlog_pos).mp hR_ge
  have hexp := Real.exp_le_exp.mpr hmul
  rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp
  have hinv : (97 / 100 : ℝ) ^ R ≤ ξ ^ 2 / 16 := by
    have hpow_pos : (0 : ℝ) < (100 / 97 : ℝ) ^ R := by positivity
    rw [show (97 / 100 : ℝ) ^ R = ((100 / 97 : ℝ) ^ R)⁻¹ by rw [← inv_pow]; norm_num]
    rw [inv_le_iff_one_le_mul₀ hpow_pos]
    rw [div_mul_eq_mul_div, one_le_div (by norm_num)]
    calc (16 : ℝ) = (16 / ξ ^ 2) * ξ ^ 2 := by field_simp
      _ ≤ (100 / 97 : ℝ) ^ R * ξ ^ 2 := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = ξ ^ 2 * (100 / 97 : ℝ) ^ R := mul_comm _ _
  exact le_trans hpow_mono hinv

/-- Upper bound on the copy count `R ≤ C_R * Real.log (1 / ξ)`. -/
lemma amplification_R_bound {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    let R : ℕ := Nat.ceil (Real.log (16 / ξ ^ 2) / Real.log (100 / 97)) + 2
    (R : ℝ) ≤ (6 / Real.log (100 / 97) + 3 / Real.log 2) * Real.log (1 / ξ) := by
  intro R
  have hinv_gt2 : 2 < 1 / ξ := by
    rw [lt_div_iff₀ hξ0]; linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : Real.log 2 ≤ Real.log (1 / ξ) := Real.log_le_log (by norm_num) hinv_gt2.le
  have h3_le : (3 : ℝ) ≤ (3 / Real.log 2) * Real.log (1 / ξ) := by
    rw [show (3 / Real.log 2) * Real.log (1 / ξ) = 3 * (Real.log (1 / ξ) / Real.log 2) by ring]
    have hdiv1 : 1 ≤ Real.log (1 / ξ) / Real.log 2 := (one_le_div hlog2_pos).mpr hlog_ge
    linarith
  have h16_le : 16 / ξ ^ 2 ≤ (1 / ξ) ^ 6 := by
    have h2pow4 : (2 : ℝ) ^ 4 ≤ (1 / ξ) ^ 4 := pow_le_pow_left₀ (by norm_num) hinv_gt2.le 4
    calc 16 / ξ ^ 2 = (2 ^ 4) * (1 / ξ) ^ 2 := by ring
      _ ≤ (1 / ξ) ^ 4 * (1 / ξ) ^ 2 := mul_le_mul_of_nonneg_right h2pow4 (by positivity)
      _ = (1 / ξ) ^ 6 := by ring
  have hlog_num : Real.log (16 / ξ ^ 2) ≤ 6 * Real.log (1 / ξ) := by
    have h := Real.log_le_log (by positivity) h16_le
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  have hlog97_pos : 0 < Real.log (100 / 97 : ℝ) := Real.log_pos (by norm_num)
  have harg_nn : 0 ≤ Real.log (16 / ξ ^ 2) / Real.log (100 / 97) := by
    have h16_gt1 : 1 < 16 / ξ ^ 2 := by
      rw [one_lt_div (by positivity)]; nlinarith
    exact div_nonneg (Real.log_nonneg h16_gt1.le) hlog97_pos.le
  have hceil := Nat.ceil_lt_add_one harg_nn
  have hR_le : (R : ℝ) ≤ Real.log (16 / ξ ^ 2) / Real.log (100 / 97) + 3 := by
    dsimp [R]; push_cast; linarith
  have hdiv_le : Real.log (16 / ξ ^ 2) / Real.log (100 / 97) ≤
      (6 / Real.log (100 / 97)) * Real.log (1 / ξ) := by
    rw [show (6 / Real.log (100 / 97)) * Real.log (1 / ξ) =
      (6 * Real.log (1 / ξ)) / Real.log (100 / 97) by ring]
    exact div_le_div_of_nonneg_right hlog_num hlog97_pos.le
  calc (R : ℝ) ≤ Real.log (16 / ξ ^ 2) / Real.log (100 / 97) + 3 := hR_le
    _ ≤ (6 / Real.log (100 / 97)) * Real.log (1 / ξ) + (3 / Real.log 2) * Real.log (1 / ξ) :=
        add_le_add hdiv_le h3_le
    _ = (6 / Real.log (100 / 97) + 3 / Real.log 2) * Real.log (1 / ξ) := by ring

/-- Eq. (179) reverse-triangle normalization bound:
for `‖u‖ = 1`, `r > 0`, `v ≠ 0`, `‖(1 / ‖v‖) • v - u‖ ≤ 2 * ‖v - r • u‖ / r`. -/
lemma normalize_approx_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v u : E} {r : ℝ} (hu : ‖u‖ = 1) (hr : 0 < r) (hv : v ≠ 0) :
    ‖((1 / ‖v‖ : ℝ) : ℂ) • v - u‖ ≤ 2 * ‖v - (r : ℂ) • u‖ / r := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hpart1 : ((1 / r : ℝ) : ℂ) • (v - (r : ℂ) • u) = ((1 / r : ℝ) : ℂ) • v - u := by
    rw [smul_sub, smul_smul, ← Complex.ofReal_mul]
    have hr1 : (1 / r : ℝ) * r = 1 := by field_simp
    rw [hr1, Complex.ofReal_one, one_smul]
  have hcoeff : (1 / ‖v‖ : ℝ) = 1 / r + (r - ‖v‖) / (r * ‖v‖) := by
    field_simp [hr.ne', hvn.ne']
    ring
  have hdecomp : ((1 / ‖v‖ : ℝ) : ℂ) • v - u =
      ((1 / r : ℝ) : ℂ) • (v - (r : ℂ) • u) +
        (((r - ‖v‖) / (r * ‖v‖) : ℝ) : ℂ) • v := by
    rw [hpart1, hcoeff, Complex.ofReal_add, add_smul]
    abel
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖((1 / r : ℝ) : ℂ) • (v - (r : ℂ) • u)‖ = ‖v - (r : ℂ) • u‖ / r := by
    rw [norm_smul, Complex.norm_of_nonneg (one_div_nonneg.mpr hr.le)]
    ring
  have h2 : ‖(((r - ‖v‖) / (r * ‖v‖) : ℝ) : ℂ) • v‖ = |r - ‖v‖| / r := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hr hvn)]
    field_simp
  have h3 : |r - ‖v‖| ≤ ‖v - (r : ℂ) • u‖ := by
    have hru : ‖(r : ℂ) • u‖ = r := by
      rw [norm_smul, Complex.norm_of_nonneg hr.le, hu, mul_one]
    calc |r - ‖v‖| = |‖(r : ℂ) • u‖ - ‖v‖| := by rw [hru]
      _ ≤ ‖(r : ℂ) • u - v‖ := abs_norm_sub_norm_le _ _
      _ = ‖v - (r : ℂ) • u‖ := norm_sub_rev _ _
  have h4 : |r - ‖v‖| / r ≤ ‖v - (r : ℂ) • u‖ / r := div_le_div_of_nonneg_right h3 hr.le
  calc ‖((1 / r : ℝ) : ℂ) • (v - (r : ℂ) • u)‖ + ‖(((r - ‖v‖) / (r * ‖v‖) : ℝ) : ℂ) • v‖
      = ‖v - (r : ℂ) • u‖ / r + |r - ‖v‖| / r := by rw [h1, h2]
    _ ≤ ‖v - (r : ℂ) • u‖ / r + ‖v - (r : ℂ) • u‖ / r := add_le_add le_rfl h4
    _ = 2 * ‖v - (r : ℂ) • u‖ / r := by ring

/-- Lower/upper amplitude bounds and normalized state error from `bandSlice` approximation. -/
lemma amplitude_window_and_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v u : E} {p ξ : ℝ} (hu : ‖u‖ = 1) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hξ0 : 0 < ξ) (_hξ1 : ξ < 1 / 2)
    (happrox : ‖v - (Real.sqrt p : ℂ) • u‖ ≤ ξ * Real.sqrt p / 4) :
    let s0 := Real.sqrt (p / 2)
    let Ft := ((1 / ‖v‖ : ℝ) : ℂ) • v
    v ≠ 0 ∧
      (7 / 8 : ℝ) * s0 ≤ (1 / Real.sqrt 2) * ‖v‖ ∧
      (1 / Real.sqrt 2) * ‖v‖ ≤ (9 / 8 : ℝ) * s0 ∧
      (1 / Real.sqrt 2) * ‖v‖ < 1 ∧
      ‖Ft‖ = 1 ∧
      ‖Ft - u‖ ≤ ξ := by
  intro s0 Ft
  let r := Real.sqrt p
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hp0
  have hs0_eq : s0 = r / Real.sqrt 2 := by
    dsimp [s0, r]; rw [Real.sqrt_div hp0.le]
  have hru : ‖(r : ℂ) • u‖ = r := by
    rw [norm_smul, Complex.norm_of_nonneg hr_pos.le, hu, mul_one]
  have hdiff : |r - ‖v‖| ≤ ξ * r / 4 := by
    calc |r - ‖v‖| = |‖(r : ℂ) • u‖ - ‖v‖| := by rw [hru]
      _ ≤ ‖(r : ℂ) • u - v‖ := abs_norm_sub_norm_le _ _
      _ = ‖v - (r : ℂ) • u‖ := norm_sub_rev _ _
      _ ≤ ξ * r / 4 := happrox
  have hv_lo : (7 / 8 : ℝ) * r ≤ ‖v‖ := by
    have := (abs_le.mp hdiff).2
    nlinarith
  have hv_hi : ‖v‖ ≤ (9 / 8 : ℝ) * r := by
    have := (abs_le.mp hdiff).1
    nlinarith
  have hv_pos : 0 < ‖v‖ := by linarith
  have hv_ne : v ≠ 0 := norm_pos_iff.mp hv_pos
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlo_s0 : (7 / 8 : ℝ) * s0 ≤ (1 / Real.sqrt 2) * ‖v‖ := by
    rw [hs0_eq]
    have h1 := mul_le_mul_of_nonneg_left hv_lo (one_div_nonneg.mpr hsqrt2_pos.le)
    calc (7 / 8 : ℝ) * (r / Real.sqrt 2) = 1 / Real.sqrt 2 * (7 / 8 * r) := by ring
      _ ≤ 1 / Real.sqrt 2 * ‖v‖ := h1
  have hhi_s0 : (1 / Real.sqrt 2) * ‖v‖ ≤ (9 / 8 : ℝ) * s0 := by
    rw [hs0_eq]
    have h1 := mul_le_mul_of_nonneg_left hv_hi (one_div_nonneg.mpr hsqrt2_pos.le)
    calc 1 / Real.sqrt 2 * ‖v‖ ≤ 1 / Real.sqrt 2 * (9 / 8 * r) := h1
      _ = (9 / 8 : ℝ) * (r / Real.sqrt 2) := by ring
  have hlt1 : (1 / Real.sqrt 2) * ‖v‖ < 1 := by
    have hr_le1 : r ≤ 1 := Real.sqrt_le_one.mpr hp1
    have h98 : (9 / 8 : ℝ) * s0 < 1 := by
      rw [hs0_eq]
      have hsq : ((9 / 8 : ℝ) / Real.sqrt 2) ^ 2 = 81 / 128 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      have hdiv_lt : (9 / 8 : ℝ) / Real.sqrt 2 < 1 := by
        nlinarith [show (0 : ℝ) < (9 / 8 : ℝ) / Real.sqrt 2 by positivity]
      calc (9 / 8 : ℝ) * (r / Real.sqrt 2) = r * ((9 / 8 : ℝ) / Real.sqrt 2) := by ring
        _ ≤ 1 * ((9 / 8 : ℝ) / Real.sqrt 2) := mul_le_mul_of_nonneg_right hr_le1 (by positivity)
        _ < 1 := by linarith
    linarith
  have hFt_norm : ‖Ft‖ = 1 := by
    change ‖((1 / ‖v‖ : ℝ) : ℂ) • v‖ = 1
    rw [norm_smul, Complex.norm_of_nonneg (one_div_nonneg.mpr hv_pos.le), one_div_mul_cancel hv_pos.ne']
  have hFt_err : ‖Ft - u‖ ≤ ξ := by
    have h1 := normalize_approx_bound hu hr_pos hv_ne
    have h2 : 2 * ‖v - (r : ℂ) • u‖ / r ≤ 2 * (ξ * r / 4) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left happrox (by norm_num)) hr_pos.le
    have h3 : 2 * (ξ * r / 4) / r = ξ / 2 := by field_simp; ring
    linarith
  exact ⟨hv_ne, hlo_s0, hhi_s0, hlt1, hFt_norm, hFt_err⟩

/-- Asymptotic gate & query bound inequalities for `n ≥ 1`. -/
lemma asymptotic_bounds_n_pos {n K D q a : ℕ} {ξ c_band C_circ : ℝ}
    (hn : 1 ≤ n) (hK : 1 ≤ K) (hD : 2 * K + 1 ≤ D) (hq : D ≤ 2 ^ q)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (_hc : 0 < c_band) (hCc : 0 < C_circ)
    (t R : ℕ)
    (ht : (2 * (t : ℝ) + 1) ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ))
    (hR : (R : ℝ) ≤ (6 / Real.log (100 / 97) + 3 / Real.log 2) * Real.log (1 / ξ)) :
    let ℓ : ℕ := Nat.clog 2 (n * D + 2) + 1
    let C_q : ℝ := max 1 (Real.pi / 2 * Real.sqrt (2 / c_band))
    let C_R : ℝ := 6 / Real.log (100 / 97) + 3 / Real.log 2
    let C_tot : ℝ := max (C_R * C_q) ((8 * C_circ / Real.log 2) * C_R * C_q)
    0 < C_tot ∧
      ((R * (2 * t + 1) : ℕ) : ℝ) ≤ C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) ∧
      ((R : ℝ) * (2 * (t : ℝ) + 2) * (C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1))) ≤
        C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
          ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by
  intro ℓ C_q C_R C_tot
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog97_pos : 0 < Real.log (100 / 97 : ℝ) := Real.log_pos (by norm_num)
  have hCq_ge1 : 1 ≤ C_q := le_max_left _ _
  have hCR_pos : 0 < C_R := by dsimp [C_R]; positivity
  have hCtot_pos : 0 < C_tot := by
    dsimp [C_tot]
    exact lt_max_of_lt_left (mul_pos hCR_pos (by linarith))
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK14_nn : 0 ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hinv_gt2 : 2 < 1 / ξ := by rw [lt_div_iff₀ hξ0]; linarith
  have hlogξ_pos : 0 < Real.log (1 / ξ) := lt_of_lt_of_le hlog2_pos (Real.log_le_log (by norm_num) hinv_gt2.le)
  have hquery : ((R * (2 * t + 1) : ℕ) : ℝ) ≤ C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) := by
    push_cast
    have hmul : (R : ℝ) * (2 * (t : ℝ) + 1) ≤ (C_R * Real.log (1 / ξ)) * (C_q * (K : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul hR ht (by positivity) (mul_nonneg hCR_pos.le hlogξ_pos.le)
    have hC1 : C_R * C_q ≤ C_tot := le_max_left _ _
    calc (R : ℝ) * (2 * (t : ℝ) + 1)
        ≤ (C_R * C_q) * ((K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ)) := by linarith
      _ ≤ C_tot * ((K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ)) :=
          mul_le_mul_of_nonneg_right hC1 (mul_nonneg hK14_nn hlogξ_pos.le)
      _ = C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) := by ring
  have hD3 : 3 ≤ D := by omega
  have hq2 : 2 ≤ q := by
    by_contra hq_lt
    have hq1 : q ≤ 1 := by omega
    have hpow : 2 ^ q ≤ 2 := by
      calc 2 ^ q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hq1
        _ = 2 := by norm_num
    omega
  have hnD3 : 3 ≤ n * D := by nlinarith
  have hlog2q : Real.log (2 ^ q) = (q : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hq_le_log : (q : ℝ) ≤ (1 / Real.log 2) * Real.log (2 ^ q) := by
    exact le_of_eq (by rw [hlog2q]; field_simp)
  have hlog2q_ge : 2 * Real.log 2 ≤ Real.log (2 ^ q) := by
    rw [hlog2q]
    have hq2r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    nlinarith
  have hlog2q_nn : 0 ≤ Real.log (2 ^ q) := by linarith
  have h1_le_log2q : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (2 ^ q) := by
    have : 1 ≤ (1 / Real.log 2) * (2 * Real.log 2) := by field_simp; norm_num
    linarith [mul_le_mul_of_nonneg_left hlog2q_ge (one_div_nonneg.mpr hlog2_pos.le)]
  have hlognD_ge : Real.log 2 ≤ Real.log (n * D) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (by omega : 2 ≤ n * D)
  have hlognD_nn : 0 ≤ Real.log (n * D) := le_trans hlog2_pos.le hlognD_ge
  have h1_le_lognD : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (n * D) := by
    rw [one_div_mul_eq_div, one_le_div hlog2_pos]; exact hlognD_ge
  have hℓ_le : (ℓ : ℝ) ≤ (4 / Real.log 2) * Real.log (n * D) := by
    let c := Nat.clog 2 (n * D + 2)
    have hc1 : 1 ≤ c := by
      dsimp [c]
      by_contra hc0
      have hcz : c = 0 := by omega
      have hle := Nat.le_pow_clog (b := 2) (by norm_num) (n * D + 2)
      change n * D + 2 ≤ 2 ^ c at hle
      rw [hcz, pow_zero] at hle
      omega
    have hpred_lt : c - 1 < c := by omega
    have hpow_lt : 2 ^ (c - 1) < n * D + 2 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
    have hpow_le : (2 : ℝ) ^ (c - 1) ≤ 2 * (n * D : ℝ) := by
      norm_cast
      omega
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (c - 1) := by positivity
    have hlog_pow : ((c - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log (n * D) := by
      have h1 := Real.log_le_log hpow_pos hpow_le
      have h2 : Real.log ((2 : ℝ) ^ (c - 1)) = ((c - 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
      have h3 : Real.log (2 * (n * D : ℝ)) = Real.log 2 + Real.log (n * D) :=
        Real.log_mul (by norm_num) (by positivity)
      linarith
    have hc_le : ((c - 1 : ℕ) : ℝ) ≤ 1 + Real.log (n * D) / Real.log 2 := by
      have hdiv := (le_div_iff₀ hlog2_pos).mpr hlog_pow
      calc ((c - 1 : ℕ) : ℝ) ≤ (Real.log 2 + Real.log (n * D)) / Real.log 2 := hdiv
        _ = 1 + Real.log (n * D) / Real.log 2 := by field_simp
    have hℓ_eq : (ℓ : ℝ) = ((c - 1 : ℕ) : ℝ) + 2 := by
      have hnat : ℓ = (c - 1) + 2 := by dsimp [ℓ, c]; omega
      rw [hnat]; push_cast; rfl
    rw [hℓ_eq]
    have h3_le : (3 : ℝ) ≤ (3 / Real.log 2) * Real.log (n * D) := by
      calc (3 : ℝ) = 3 * 1 := by ring
        _ ≤ 3 * ((1 / Real.log 2) * Real.log (n * D)) := mul_le_mul_of_nonneg_left h1_le_lognD (by norm_num)
        _ = (3 / Real.log 2) * Real.log (n * D) := by ring
    have hdiv_eq : Real.log (n * D) / Real.log 2 = (1 / Real.log 2) * Real.log (n * D) := by ring
    calc ((c - 1 : ℕ) : ℝ) + 2 ≤ 3 + (1 / Real.log 2) * Real.log (n * D) := by linarith
      _ ≤ (3 / Real.log 2) * Real.log (n * D) + (1 / Real.log 2) * Real.log (n * D) := add_le_add h3_le le_rfl
      _ = (4 / Real.log 2) * Real.log (n * D) := by ring
  have hinner : (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1 ≤
      (4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1_le_nlog : (1 : ℝ) ≤ (n : ℝ) * ((1 / Real.log 2) * Real.log (2 ^ q)) := by
      have h1 : 1 * 1 ≤ (n : ℝ) * ((1 / Real.log 2) * Real.log (2 ^ q)) :=
        mul_le_mul hn_ge1 h1_le_log2q (by norm_num) (by positivity)
      linarith
    have hq1_le : (q : ℝ) + 1 ≤ (2 / Real.log 2) * Real.log (2 ^ q) := by
      calc (q : ℝ) + 1 ≤ (1 / Real.log 2) * Real.log (2 ^ q) + (1 / Real.log 2) * Real.log (2 ^ q) :=
            add_le_add hq_le_log h1_le_log2q
        _ = (2 / Real.log 2) * Real.log (2 ^ q) := by ring
    have hlog_lt1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
    have h4_ge1 : (1 : ℝ) ≤ 4 / Real.log 2 := by
      rw [one_le_div hlog2_pos]; linarith
    have ha_le : (a : ℝ) ≤ (4 / Real.log 2) * (a : ℝ) := by
      have h1 : 1 * (a : ℝ) ≤ (4 / Real.log 2) * (a : ℝ) :=
        mul_le_mul_of_nonneg_right h4_ge1 (Nat.cast_nonneg a)
      linarith
    have hn_mul : (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + 1 ≤
        (4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D))) := by
      have hsum : (q : ℝ) + (ℓ : ℝ) + 1 ≤
          (2 / Real.log 2) * Real.log (2 ^ q) + (4 / Real.log 2) * Real.log (n * D) := by linarith
      have hmul : (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) ≤
          (n : ℝ) * ((2 / Real.log 2) * Real.log (2 ^ q) + (4 / Real.log 2) * Real.log (n * D)) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)
      calc (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + 1
          ≤ (n : ℝ) * ((2 / Real.log 2) * Real.log (2 ^ q) + (4 / Real.log 2) * Real.log (n * D)) +
              (n : ℝ) * ((1 / Real.log 2) * Real.log (2 ^ q)) := add_le_add hmul h1_le_nlog
        _ = (n : ℝ) * ((3 / Real.log 2) * Real.log (2 ^ q) + (4 / Real.log 2) * Real.log (n * D)) := by ring
        _ ≤ (n : ℝ) * ((4 / Real.log 2) * Real.log (2 ^ q) + (4 / Real.log 2) * Real.log (n * D)) := by
            have h34 : (3 / Real.log 2) * Real.log (2 ^ q) ≤ (4 / Real.log 2) * Real.log (2 ^ q) := by
              have hnn : 0 ≤ Real.log (2 ^ q) / Real.log 2 := div_nonneg hlog2q_nn hlog2_pos.le
              calc (3 / Real.log 2) * Real.log (2 ^ q) = 3 * (Real.log (2 ^ q) / Real.log 2) := by ring
                _ ≤ 4 * (Real.log (2 ^ q) / Real.log 2) := by linarith
                _ = (4 / Real.log 2) * Real.log (2 ^ q) := by ring
            exact mul_le_mul_of_nonneg_left (add_le_add h34 le_rfl) (Nat.cast_nonneg n)
        _ = (4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D))) := by ring
    calc (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1
        = ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + 1) + (a : ℝ) := by ring
      _ ≤ (4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D))) +
            (4 / Real.log 2) * (a : ℝ) := add_le_add hn_mul ha_le
      _ = (4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by ring
  have hgate :
      ((R : ℝ) * (2 * (t : ℝ) + 2) * (C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1))) ≤
        C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
          ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by
    have h2t2 : 2 * (t : ℝ) + 2 ≤ 2 * (2 * (t : ℝ) + 1) := by linarith
    have hRt : (R : ℝ) * (2 * (t : ℝ) + 2) ≤ 2 * (C_R * C_q * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ)) := by
      have h1 : (R : ℝ) * (2 * (t : ℝ) + 2) ≤ (R : ℝ) * (2 * (2 * (t : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h2t2 (Nat.cast_nonneg R)
      have h2 : (R : ℝ) * (2 * (t : ℝ) + 1) ≤ C_R * C_q * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) := by
        have hmul := mul_le_mul hR ht (by positivity) (mul_nonneg hCR_pos.le hlogξ_pos.le)
        linarith
      linarith
    have hB_le : C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1) ≤
        (4 * C_circ / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by
      have h := mul_le_mul_of_nonneg_left hinner hCc.le
      calc C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1)
          ≤ C_circ * ((4 / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a)) := h
        _ = (4 * C_circ / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by ring
    have hB_nn : 0 ≤ C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1) := by positivity
    have hRt_nn : 0 ≤ 2 * (C_R * C_q * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ)) := by positivity
    have hRHS_nn : 0 ≤ (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a := by positivity
    have hmul := mul_le_mul hRt hB_le hB_nn hRt_nn
    have hC2 : (8 * C_circ / Real.log 2) * C_R * C_q ≤ C_tot := le_max_right _ _
    calc (R : ℝ) * (2 * (t : ℝ) + 2) * (C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1))
        ≤ (2 * (C_R * C_q * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ))) *
            ((4 * C_circ / Real.log 2) * ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a)) := hmul
      _ = ((8 * C_circ / Real.log 2) * C_R * C_q) * ((K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
            ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a)) := by ring
      _ ≤ C_tot * ((K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
            ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a)) :=
          mul_le_mul_of_nonneg_right hC2 (mul_nonneg (mul_nonneg hK14_nn hlogξ_pos.le) hRHS_nn)
      _ = C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
            ((n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) + a) := by ring
  exact ⟨hCtot_pos, hquery, hgate⟩

/-! ### 2. Linear-Algebra, `embedOp`, and `OracleCircuit` Helpers -/

lemma act_one_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext y; simp [act]

lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

lemma act_sub {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ - φ) = act U ψ - act U φ := by
  ext y; simp [act, Matrix.mulVec_sub]

lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma act_neg {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (-ψ) = -act U ψ := by
  ext y; simp [act, Matrix.mulVec_neg]

lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

lemma act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ι) :
    act M (ket z) = ∑ y : ι, M y z • ket y := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z, Finset.sum_eq_single y]
  · simp
  · intro x _ hx; simp [hx.symm]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma inner_ket_left {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι) (ψ : EuclideanSpace ℂ ι) :
    inner ℂ (ket z) ψ = ψ z := by
  simp [ket, EuclideanSpace.inner_single_left]

lemma inner_act_star {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (φ ψ : EuclideanSpace ℂ ι) :
    inner ℂ (act A φ) ψ = inner ℂ φ (act (star A) ψ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, act, Matrix.mulVec, dotProduct,
    Matrix.star_apply, Complex.star_def, map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    ring

lemma vec_eq_sum_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ψ = ∑ z : ι, ψ z • ket z := by
  ext y
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ket, PiLp.single_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [hz.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma norm_sq_eq_sum {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    ‖ψ‖ ^ 2 = ∑ z : ι, ‖ψ z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

lemma probEvent_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι)
    (P : ι → Prop) [DecidablePred P] :
    probEvent ψ P = ∑ z ∈ Finset.univ.filter P, ‖ψ z‖ ^ 2 := by
  dsimp only [probEvent, prob]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [inner_ket_left]

lemma embedOp_comp {k m₀ m : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin m₀) (emb : Fin m₀ ↪ Fin m) :
    embedOp (embedOp M w) emb = embedOp M (w.trans emb) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hout : ∀ a : Fin m, a ∉ Set.range (w.trans emb) → y a = z a
  · rw [if_pos hout]
    have hout_emb : ∀ a : Fin m, a ∉ Set.range emb → y a = z a := fun a ha =>
      hout a fun ⟨i, hi⟩ => ha ⟨w i, hi⟩
    rw [if_pos hout_emb]
    have hout_w : ∀ b : Fin m₀, b ∉ Set.range w → (y ∘ emb) b = (z ∘ emb) b := fun b hb =>
      hout (emb b) fun ⟨i, hi⟩ => hb ⟨i, emb.injective hi⟩
    rw [if_pos hout_w]
    rfl
  · rw [if_neg hout]
    split_ifs with h1 h2
    · exfalso; apply hout; intro a ha
      by_cases hae : a ∈ Set.range emb
      · obtain ⟨b, rfl⟩ := hae
        exact h2 b fun ⟨i, hi⟩ => ha ⟨i, by simp [hi]⟩
      · exact h1 a hae
    · rfl
    · rfl

noncomputable def updateOn {k n : ℕ} (emb : Fin k ↪ Fin n) (y : Qubits n) (u : Qubits k) :
    Qubits n :=
  fun i => open Classical in if h : ∃ j, emb j = i then u (Classical.choose h) else y i

lemma updateOn_comp {k n : ℕ} (emb : Fin k ↪ Fin n) (y : Qubits n) (u : Qubits k) :
    updateOn emb y u ∘ emb = u := by
  classical
  funext j
  have h : ∃ j', emb j' = emb j := ⟨j, rfl⟩
  change (if h' : ∃ j', emb j' = emb j then u (Classical.choose h') else y (emb j)) = u j
  rw [dif_pos h, emb.injective (Classical.choose_spec h)]

lemma updateOn_apply {k n : ℕ} (emb : Fin k ↪ Fin n) (y : Qubits n) (u : Qubits k) (j : Fin k) :
    updateOn emb y u (emb j) = u j :=
  congrFun (updateOn_comp emb y u) j

lemma updateOn_off {k n : ℕ} (emb : Fin k ↪ Fin n) (y : Qubits n) (u : Qubits k)
    {i : Fin n} (hi : i ∉ Set.range emb) :
    updateOn emb y u i = y i := by
  classical
  have h : ¬ ∃ j, emb j = i := hi
  change (if h' : ∃ j, emb j = i then u (Classical.choose h') else y i) = y i
  rw [dif_neg h]

lemma updateOn_inj {k n : ℕ} (emb : Fin k ↪ Fin n) (y : Qubits n) :
    Function.Injective (updateOn emb y) := by
  intro u₁ u₂ h
  have := congrArg (· ∘ emb) h
  simpa [updateOn_comp] using this

lemma eq_updateOn_of_agree {k n : ℕ} (emb : Fin k ↪ Fin n) {y z : Qubits n}
    (hz : ∀ a : Fin n, a ∉ Set.range emb → y a = z a) :
    z = updateOn emb y (z ∘ emb) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range emb
  · obtain ⟨j, rfl⟩ := ha
    exact (updateOn_apply emb y (z ∘ emb) j).symm
  · rw [updateOn_off emb y _ ha, hz a ha]

lemma embedOp_mul {k m : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  classical
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hout : ∀ a : Fin m, a ∉ Set.range w → y a = z a
  · rw [if_pos hout]
    have hsum : (∑ u : Qubits m,
          (if ∀ a, a ∉ Set.range w → y a = u a then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
        ∑ u ∈ Finset.univ.image (updateOn w z),
          (if ∀ a, a ∉ Set.range w → y a = u a then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro u _ hu
      have hne : ¬ ∀ a, a ∉ Set.range w → u a = z a := by
        intro huz; apply hu; rw [Finset.mem_image]
        exact ⟨u ∘ w, Finset.mem_univ _, (eq_updateOn_of_agree w fun a ha => (huz a ha).symm).symm⟩
      rw [if_neg hne, mul_zero]
    rw [hsum, Finset.sum_image (fun x₁ _ x₂ _ h => updateOn_inj w z h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hy : ∀ a : Fin m, a ∉ Set.range w → y a = updateOn w z x a := fun a ha =>
      (hout a ha).trans (updateOn_off w z x ha).symm
    have hz : ∀ a : Fin m, a ∉ Set.range w → updateOn w z x a = z a := fun a ha =>
      updateOn_off w z x ha
    rw [if_pos hy, if_pos hz, updateOn_comp]
  · rw [if_neg hout]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = u a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → u a = z a := fun h2' =>
        hout fun a ha => (h1 a ha).trans (h2' a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_star {k n : ℕ} (A : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star A) w = star (embedOp A w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun hzy =>
      h fun a ha => (hzy a ha).symm
    rw [if_neg h, if_neg h', star_zero]

lemma embedOp_mem_unitaryGroup {k n : ℕ} {A : Matrix (Qubits k) (Qubits k) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp A w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ← embedOp_star, ← embedOp_mul,
    Matrix.mem_unitaryGroup_iff.mp hA, embedOp_one]

lemma act_embedOp_apply {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (emb : Fin k ↪ Fin n) (ψ : EuclideanSpace ℂ (Qubits n)) (y : Qubits n) :
    act (embedOp M emb) ψ y = ∑ u : Qubits k, M (y ∘ emb) u * ψ (updateOn emb y u) := by
  classical
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply]
  have hsub : (∑ z : Qubits n, (if ∀ a, a ∉ Set.range emb → y a = z a then M (y ∘ emb) (z ∘ emb) else 0) * ψ z) =
      ∑ z ∈ Finset.univ.image (updateOn emb y),
        (if ∀ a, a ∉ Set.range emb → y a = z a then M (y ∘ emb) (z ∘ emb) else 0) * ψ z := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro z _ hz
    by_cases hagree : ∀ a, a ∉ Set.range emb → y a = z a
    · exfalso; apply hz; rw [Finset.mem_image]
      exact ⟨z ∘ emb, Finset.mem_univ _, (eq_updateOn_of_agree emb hagree).symm⟩
    · rw [if_neg hagree, zero_mul]
  rw [hsub, Finset.sum_image (fun u₁ _ u₂ _ h => updateOn_inj emb y h)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hagree : ∀ a, a ∉ Set.range emb → y a = updateOn emb y u a := fun a ha =>
    (updateOn_off emb y u ha).symm
  rw [if_pos hagree, updateOn_comp]

lemma act_embedOp_ket_map {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (emb : Fin k ↪ Fin n) (z : Qubits n) (α : ℂ) (x' : Qubits k)
    (hact : act M (ket (z ∘ emb)) = α • ket x') :
    act (embedOp M emb) (ket z) = α • ket (updateOn emb z x') := by
  ext y
  rw [act_embedOp_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ket, PiLp.single_apply]
  have hM : M (y ∘ emb) (z ∘ emb) = α * (if y ∘ emb = x' then 1 else 0) := by
    have hy := congrFun (congrArg WithLp.ofLp hact) (y ∘ emb)
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at hy
    rw [Finset.sum_eq_single (z ∘ emb)] at hy
    · simpa using hy
    · intro v _ hv; simp [hv]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (z ∘ emb)]
  · by_cases hout : ∀ a, a ∉ Set.range emb → y a = z a
    · have hup : updateOn emb y (z ∘ emb) = z :=
        (eq_updateOn_of_agree emb fun a ha => hout a ha).symm
      rw [hup, if_pos rfl, mul_one, hM]
      have heq : (y = updateOn emb z x') ↔ (y ∘ emb = x') := by
        constructor
        · intro h; rw [h, updateOn_comp]
        · intro h; funext a
          by_cases ha : a ∈ Set.range emb
          · obtain ⟨j, rfl⟩ := ha; exact (congrFun h j).trans (updateOn_apply emb z x' j).symm
          · exact (hout a ha).trans (updateOn_off emb z x' ha).symm
      by_cases hyz : y = updateOn emb z x'
      · rw [if_pos hyz, if_pos (heq.mp hyz)]
      · rw [if_neg hyz, if_neg (fun h => hyz (heq.mpr h)), mul_zero]
    · push Not at hout
      obtain ⟨a, ha1, ha2⟩ := hout
      have hne_up : updateOn emb y (z ∘ emb) ≠ z := fun h =>
        ha2 (by simpa [updateOn_off emb y _ ha1] using congrFun h a)
      have hne_y : y ≠ updateOn emb z x' := fun h =>
        ha2 (by simpa [updateOn_off emb z _ ha1] using congrFun h a)
      simp [hne_up, hne_y]
  · intro u _ hu
    have hne : updateOn emb y u ≠ z := fun h => hu (by rw [← h, updateOn_comp])
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

def embedCircuit {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    Circuit S m :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans emb⟩

lemma embedCircuit_length {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    (embedCircuit emb c).length = c.length :=
  List.length_map _

lemma embedCircuit_unitary {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    (embedCircuit emb c).unitary = embedOp c.unitary emb := by
  unfold Circuit.unitary embedCircuit
  induction c with
  | nil => simp [embedOp_one]
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    rw [ih, embedOp_mul, embedOp_comp]

lemma circuit_unitary_append {S : Set Gate} {m : ℕ} (c₁ c₂ : Circuit S m) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma circuit_unitary_mem_unitaryGroup {m : ℕ} (c : Circuit gates12 m) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  unfold Circuit.unitary
  induction c with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    exact Submonoid.mul_mem _ ih (embedOp_mem_unitaryGroup g.mem.1 g.wires)

def embedOracleStep {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) : OracleStep S a m₀ → OracleStep S a m
  | .gate g => .gate ⟨g.gate, g.mem, g.wires.trans emb⟩
  | .query k adj none wires _ => .query k adj none (wires.trans emb) (by simp)
  | .query k adj (some ctl) wires hc =>
      .query k adj (some (emb ctl)) (wires.trans emb) (fun c hc' => by
        obtain rfl := Option.some.inj hc'.symm
        rintro ⟨i, hi⟩
        exact hc ctl rfl ⟨i, emb.injective hi⟩)

def embedOracleCircuit {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) (c : OracleCircuit S a m₀) : OracleCircuit S a m :=
  c.map (embedOracleStep emb)

lemma embedOracleCircuit_uncontrolled {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) {c : OracleCircuit S a m₀} (hc : Uncontrolled c) :
    Uncontrolled (embedOracleCircuit emb c) := by
  intro st hst
  simp only [embedOracleCircuit, List.mem_map] at hst
  rcases hst with ⟨st₀, hst₀, rfl⟩
  have h0 := hc st₀ hst₀
  cases st₀ with
  | gate g => trivial
  | query k adj ctl wires hcw =>
    dsimp only at h0
    subst h0
    rfl

lemma embedOracleCircuit_queryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) (c : OracleCircuit S a m₀) (k : Fin r) :
    (embedOracleCircuit emb c).queryCount k = c.queryCount k := by
  induction c with
  | nil => simp [embedOracleCircuit, OracleCircuit.queryCount]
  | cons st rest ih =>
    simp only [embedOracleCircuit, List.map_cons, OracleCircuit.queryCount, List.countP_cons] at ih ⊢
    rcases st with g | ⟨k', adj, ctl, wires, hcw⟩
    · simp [embedOracleStep, OracleStep.IsQueryTo, ih]
    · cases ctl <;> simp [embedOracleStep, OracleStep.IsQueryTo, ih]

lemma embedOracleCircuit_gateCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) (c : OracleCircuit S a m₀) :
    (embedOracleCircuit emb c).gateCount = c.gateCount := by
  induction c with
  | nil => simp [embedOracleCircuit, OracleCircuit.gateCount]
  | cons st rest ih =>
    simp only [embedOracleCircuit, List.map_cons, OracleCircuit.gateCount, List.countP_cons] at ih ⊢
    rcases st with g | ⟨k', adj, ctl, wires, hcw⟩
    · simp [embedOracleStep, ih]
    · cases ctl <;> simp [embedOracleStep, ih]

lemma embedOracleCircuit_unitary_of_uncontrolled {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) {c : OracleCircuit S a m₀} (hc : Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (embedOracleCircuit emb c).unitary orc = embedOp (c.unitary orc) emb := by
  induction c with
  | nil => simp [embedOracleCircuit, OracleCircuit.unitary, embedOp_one]
  | cons st rest ih =>
    have hrest : Uncontrolled rest := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have hst := hc st List.mem_cons_self
    simp only [embedOracleCircuit, List.map_cons, OracleCircuit.unitary, List.reverse_cons,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    rw [ih hrest]
    have hm : OracleStep.mat orc (embedOracleStep emb st) = embedOp (OracleStep.mat orc st) emb := by
      rcases st with g | ⟨k, adj, ctl, wires, hcw⟩
      · exact (embedOp_comp g.gate.mat g.wires emb).symm
      · dsimp only at hst
        subst hst
        exact (embedOp_comp _ wires emb).symm
    rw [hm, ← embedOp_mul]

lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (c₁ ++ c₂).unitary orc = c₂.unitary orc * c₁.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) (k : Fin r) :
    (c₁ ++ c₂).queryCount k = c₁.queryCount k + c₂.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

lemma oracleCircuit_gateCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) :
    (c₁ ++ c₂).gateCount = c₁.gateCount + c₂.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

lemma oracleCircuit_unitary_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c.map OracleStep.gate : OracleCircuit S a m) orc = c.unitary := by
  simp [OracleCircuit.unitary, Circuit.unitary, Function.comp_def, OracleStep.mat]

lemma oracleCircuit_queryCount_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) (k : Fin r) :
    OracleCircuit.queryCount (c.map OracleStep.gate : OracleCircuit S a m) k = 0 := by
  simp [OracleCircuit.queryCount, List.countP_map, Function.comp_def, OracleStep.IsQueryTo]

lemma oracleCircuit_gateCount_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) :
    OracleCircuit.gateCount (c.map OracleStep.gate : OracleCircuit S a m) = c.length := by
  simp [OracleCircuit.gateCount, List.countP_map, Function.comp_def]

lemma uncontrolled_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (c : Circuit S m) :
    Uncontrolled (c.map OracleStep.gate : OracleCircuit S a m) := by
  intro st hst
  simp only [List.mem_map] at hst
  rcases hst with ⟨g, _, rfl⟩
  trivial

lemma oracleCircuit_unitary_mem_unitaryGroup_of_uncontrolled {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    {c : OracleCircuit gates12 a m} (hc : Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ) :
    c.unitary orc ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  induction c with
  | nil => simp [OracleCircuit.unitary]
  | cons st rest ih =>
    have hrest : Uncontrolled rest := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have hst := hc st List.mem_cons_self
    simp only [OracleCircuit.unitary, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    refine Submonoid.mul_mem _ (ih hrest) ?_
    rcases st with g | ⟨k, adj, ctl, wires, hcw⟩
    · exact embedOp_mem_unitaryGroup g.mem.1 g.wires
    · dsimp only at hst
      subst hst
      apply embedOp_mem_unitaryGroup
      cases adj
      · simpa using horc k
      · simpa using Unitary.star_mem (horc k)

/-! ### 3. Clean Ancilla Lifting & Single-Copy Grover Rotation Lemma -/

def padFalse (W anc : ℕ) (x : Qubits W) : Qubits (W + anc) :=
  Fin.append x (fun _ : Fin anc => false)

@[simp] lemma padFalse_castAdd (W anc : ℕ) (x : Qubits W) (i : Fin W) :
    padFalse W anc x (Fin.castAdd anc i) = x i :=
  Fin.append_left x _ i

@[simp] lemma padFalse_natAdd (W anc : ℕ) (x : Qubits W) (j : Fin anc) :
    padFalse W anc x (Fin.natAdd W j) = false :=
  Fin.append_right x _ j

lemma padFalse_inj (W anc : ℕ) : Function.Injective (padFalse W anc) := by
  intro x₁ x₂ h
  funext i
  have := congrFun h (Fin.castAdd anc i)
  simpa using this

lemma eq_padFalse_of_clean {W anc : ℕ} (z : Qubits (W + anc))
    (hz : ∀ j : Fin anc, z (Fin.natAdd W j) = false) :
    z = padFalse W anc (fun i => z (Fin.castAdd anc i)) := by
  funext w
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · simp [padFalse]
  · simp [padFalse, hz j]

def padFalseEmb (W anc₁ anc₂ : ℕ) (h : anc₁ ≤ anc₂) : Fin (W + anc₁) ↪ Fin (W + anc₂) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b hab := Fin.ext (by have := congrArg Fin.val hab; exact this)

lemma padFalse_circuit_act {W anc₁ anc₂ : ℕ} (h : anc₁ ≤ anc₂)
    (c : Circuit gates12 (W + anc₁)) (α : Qubits W → ℂ) (f : Qubits W → Qubits W)
    (hc : ∀ x : Qubits W, act c.unitary (ket (padFalse W anc₁ x)) = α x • ket (padFalse W anc₁ (f x))) :
    ∀ x : Qubits W,
      act (embedCircuit (padFalseEmb W anc₁ anc₂ h) c).unitary (ket (padFalse W anc₂ x)) =
        α x • ket (padFalse W anc₂ (f x)) := by
  intro x
  rw [embedCircuit_unitary]
  let emb := padFalseEmb W anc₁ anc₂ h
  have hcomp : padFalse W anc₂ x ∘ emb = padFalse W anc₁ x := by
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · have h1 : emb (Fin.castAdd anc₁ i) = Fin.castAdd anc₂ i := Fin.ext rfl
      rw [Function.comp_apply, h1, padFalse_castAdd, padFalse_castAdd]
    · have h1 : emb (Fin.natAdd W j) = Fin.natAdd W ⟨j.1, by omega⟩ := Fin.ext rfl
      rw [Function.comp_apply, h1, padFalse_natAdd, padFalse_natAdd]
  have hact' : act c.unitary (ket (padFalse W anc₂ x ∘ emb)) = α x • ket (padFalse W anc₁ (f x)) := by
    rw [hcomp]; exact hc x
  have hres := act_embedOp_ket_map c.unitary emb (padFalse W anc₂ x) (α x) (padFalse W anc₁ (f x)) hact'
  have hup : updateOn emb (padFalse W anc₂ x) (padFalse W anc₁ (f x)) = padFalse W anc₂ (f x) := by
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · have h1 : Fin.castAdd anc₂ i = emb (Fin.castAdd anc₁ i) := Fin.ext rfl
      rw [h1, updateOn_apply, padFalse_castAdd, ← h1, padFalse_castAdd]
    · by_cases hj : j.1 < anc₁
      · have h1 : Fin.natAdd W j = emb (Fin.natAdd W ⟨j.1, hj⟩) := Fin.ext rfl
        rw [h1, updateOn_apply, padFalse_natAdd, ← h1, padFalse_natAdd]
      · have hnot : Fin.natAdd W j ∉ Set.range emb := by
          rintro ⟨u, hu⟩
          have hu1 := congrArg Fin.val hu
          change u.1 = W + j.1 at hu1
          have huLt := u.isLt
          omega
        rw [updateOn_off emb _ _ hnot, padFalse_natAdd, padFalse_natAdd]
  rwa [hup] at hres

noncomputable def liftClean (W anc : ℕ) (φ : EuclideanSpace ℂ (Qubits W)) :
    EuclideanSpace ℂ (Qubits (W + anc)) :=
  ∑ x : Qubits W, φ x • ket (padFalse W anc x)

lemma liftClean_ket (W anc : ℕ) (z : Qubits W) :
    liftClean W anc (ket z) = ket (padFalse W anc z) := by
  dsimp [liftClean]
  rw [Finset.sum_eq_single z]
  · simp [ket]
  · intro x _ hx; simp [ket, hx.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma liftClean_zeroKet (W anc : ℕ) :
    liftClean W anc (zeroKet W) = zeroKet (W + anc) := by
  dsimp [zeroKet]
  rw [liftClean_ket]
  congr 1
  funext w
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · simp [padFalse]
  · simp [padFalse]

lemma liftClean_apply {W anc : ℕ} (φ : EuclideanSpace ℂ (Qubits W)) (z : Qubits (W + anc)) :
    liftClean W anc φ z =
      if ∀ j : Fin anc, z (Fin.natAdd W j) = false then φ (fun i => z (Fin.castAdd anc i)) else 0 := by
  classical
  dsimp [liftClean]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ket, PiLp.single_apply]
  by_cases hz : ∀ j : Fin anc, z (Fin.natAdd W j) = false
  · rw [if_pos hz]
    have hz_eq := eq_padFalse_of_clean z hz
    rw [Finset.sum_eq_single (fun i => z (Fin.castAdd anc i))]
    · rw [if_pos hz_eq, mul_one]
    · intro x _ hx
      have hne : z ≠ padFalse W anc x := fun h => hx (padFalse_inj W anc (hz_eq.symm.trans h)).symm
      rw [if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hz]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : z ≠ padFalse W anc x := fun h => hz fun j => by rw [h, padFalse_natAdd]
    rw [if_neg hne, mul_zero]

lemma act_embedOp_liftClean {W anc : ℕ} (U : Matrix (Qubits W) (Qubits W) ℂ)
    (φ : EuclideanSpace ℂ (Qubits W)) :
    act (embedOp U (Fin.castAddEmb anc)) (liftClean W anc φ) = liftClean W anc (act U φ) := by
  dsimp only [liftClean]
  rw [act_sum]
  have hterm : ∀ x : Qubits W,
      act (embedOp U (Fin.castAddEmb anc)) (φ x • ket (padFalse W anc x)) =
        ∑ y : Qubits W, (U y x * φ x) • ket (padFalse W anc y) := by
    intro x
    rw [act_smul]
    have hket : act (embedOp U (Fin.castAddEmb anc)) (ket (padFalse W anc x)) =
        ∑ y : Qubits W, U y x • ket (padFalse W anc y) := by
      ext z
      rw [act_embedOp_apply]
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        ket, PiLp.single_apply]
      rw [Finset.sum_eq_single x]
      · have hup : updateOn (Fin.castAddEmb anc) z x =
            Fin.append x (fun j => z (Fin.natAdd W j)) := by
          funext w
          refine Fin.addCases ?_ ?_ w
          · intro i
            have h1 : Fin.castAdd anc i = (Fin.castAddEmb anc) i := rfl
            rw [h1, updateOn_apply, ← h1, Fin.append_left]
          · intro j
            have hnot : Fin.natAdd W j ∉ Set.range (Fin.castAddEmb anc) := by
              rintro ⟨i, hi⟩
              have := congrArg Fin.val hi
              change i.1 = W + j.1 at this
              omega
            rw [updateOn_off _ _ _ hnot, Fin.append_right]
        by_cases hclean : ∀ j : Fin anc, z (Fin.natAdd W j) = false
        · have hz_pad : z = padFalse W anc (fun i => z (Fin.castAdd anc i)) :=
            eq_padFalse_of_clean z hclean
          have hup_pad : updateOn (Fin.castAddEmb anc) z x = padFalse W anc x := by
            rw [hup]; funext w
            refine Fin.addCases (fun i => by simp [padFalse]) (fun j => by simp [padFalse, hclean j]) w
          rw [hup_pad, if_pos rfl, mul_one]
          rw [Finset.sum_eq_single (fun i => z (Fin.castAdd anc i))]
          · rw [if_pos hz_pad, mul_one]
            change U (fun i => z (Fin.castAdd anc i)) x = U (fun i => z (Fin.castAdd anc i)) x
            rfl
          · intro y _ hy
            have hne : z ≠ padFalse W anc y := fun h => hy (padFalse_inj W anc (hz_pad.symm.trans h)).symm
            rw [if_neg hne, mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · have hne1 : updateOn (Fin.castAddEmb anc) z x ≠ padFalse W anc x := fun h =>
            hclean fun j => by simpa [hup] using congrFun h (Fin.natAdd W j)
          rw [if_neg hne1, mul_zero]
          symm
          refine Finset.sum_eq_zero fun y _ => ?_
          have hne2 : z ≠ padFalse W anc y := fun h => hclean fun j => by rw [h, padFalse_natAdd]
          rw [if_neg hne2, mul_zero]
      · intro u _ hu
        have hne : updateOn (Fin.castAddEmb anc) z u ≠ padFalse W anc x := by
          intro h
          apply hu
          funext i
          have hi := congrFun h (Fin.castAdd anc i)
          have h1 : Fin.castAdd anc i = (Fin.castAddEmb anc) i := rfl
          rw [h1, updateOn_apply, ← h1, padFalse_castAdd] at hi
          exact hi
        rw [if_neg hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hket, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_smul, mul_comm (φ x)]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1

lemma act_clean_diag_liftClean {W anc : ℕ} (c : Circuit gates12 (W + anc))
    (α : Qubits W → ℂ)
    (hc : ∀ x : Qubits W, act c.unitary (ket (padFalse W anc x)) = α x • ket (padFalse W anc x))
    (φ : EuclideanSpace ℂ (Qubits W)) :
    act c.unitary (liftClean W anc φ) = liftClean W anc (act (Matrix.diagonal α) φ) := by
  dsimp only [liftClean]
  rw [act_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [act_smul, hc x, smul_smul]
  congr 1
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_diagonal]
  ring

lemma liftClean_good_bad {W anc : ℕ} (good : Qubits W → Bool)
    (ψ_good ψ_bad : EuclideanSpace ℂ (Qubits W))
    (hg : ∀ z, ¬ good z → ψ_good z = 0)
    (hb : ∀ z, good z → ψ_bad z = 0)
    (c a b : ℂ) :
    liftClean W anc (c • (a • ψ_good + b • ψ_bad)) =
      ∑ z : Qubits W, (c * (if good z then a * ψ_good z else b * ψ_bad z)) • ket (padFalse W anc z) := by
  dsimp only [liftClean]
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  simp only [WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases hz : good z
  · simp [hz, hb z hz]
  · simp [hz, hg z hz]

/-- 2D real Grover rotation lemma on `Qubits W`. -/
lemma grover_iter_2d {W : ℕ} (A : Matrix (Qubits W) (Qubits W) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits W) ℂ)
    (good : Qubits W → Bool) (t : ℕ) :
    let φ0 := act A (zeroKet W)
    let φ_good : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then φ0 z else 0
    let φ_bad : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then 0 else φ0 z
    0 < ‖φ_good‖ → 0 < ‖φ_bad‖ →
    let θ := Real.arcsin ‖φ_good‖
    let ψ_good := ((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good
    let ψ_bad := ((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad
    let S_good : Matrix (Qubits W) (Qubits W) ℂ :=
      Matrix.diagonal fun z => if good z then (-1 : ℂ) else 1
    let S_zero : Matrix (Qubits W) (Qubits W) ℂ :=
      Matrix.diagonal fun z => if z = (fun _ => false) then (-1 : ℂ) else 1
    let G := A * S_zero * star A * S_good
    act (G ^ t) φ0 =
      ((-1 : ℂ) ^ t) • ((Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) • ψ_good +
        (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) • ψ_bad) := by
  intro φ0 φ_good φ_bad hgp hbp θ ψ_good ψ_bad S_good S_zero G
  have hφ0_norm : ‖φ0‖ = 1 := by
    dsimp [φ0]
    rw [act_norm_of_mem_unitaryGroup hA]
    simp [zeroKet, ket]
  have hsum_sq : ‖φ_good‖ ^ 2 + ‖φ_bad‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    have hsplit : ∀ z : Qubits W, ‖φ_good z‖ ^ 2 + ‖φ_bad z‖ ^ 2 = ‖φ0 z‖ ^ 2 := fun z => by
      dsimp [φ_good, φ_bad]; split_ifs <;> simp
    rw [← Finset.sum_add_distrib]
    simp_rw [hsplit]
    rw [← norm_sq_eq_sum, hφ0_norm, one_pow]
  have hgp_le1 : ‖φ_good‖ ≤ 1 := by
    nlinarith [sq_nonneg ‖φ_bad‖]
  have hsinθ : Real.sin θ = ‖φ_good‖ :=
    Real.sin_arcsin (by linarith) hgp_le1
  have hcosθ : Real.cos θ = ‖φ_bad‖ := by
    rw [Real.cos_arcsin]
    have h1 : 1 - ‖φ_good‖ ^ 2 = ‖φ_bad‖ ^ 2 := by linarith
    rw [h1, Real.sqrt_sq hbp.le]
  have hψg_norm : ‖ψ_good‖ = 1 := by
    change ‖((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good‖ = 1
    rw [norm_smul, Complex.norm_of_nonneg (one_div_nonneg.mpr hgp.le), one_div_mul_cancel hgp.ne']
  have hψb_norm : ‖ψ_bad‖ = 1 := by
    change ‖((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad‖ = 1
    rw [norm_smul, Complex.norm_of_nonneg (one_div_nonneg.mpr hbp.le), one_div_mul_cancel hbp.ne']
  have hψg_ψb : inner ℂ ψ_good ψ_bad = 0 := by
    change inner ℂ (((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good) (((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad) = 0
    rw [inner_smul_left, inner_smul_right]
    have hin : inner ℂ φ_good φ_bad = 0 := by
      simp only [PiLp.inner_apply, RCLike.inner_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      dsimp [φ_good, φ_bad]; split_ifs <;> simp
    rw [hin, mul_zero, mul_zero]
  have hψb_ψg : inner ℂ ψ_bad ψ_good = 0 := by
    rw [← inner_conj_symm, hψg_ψb, map_zero]
  have hψg_self : inner ℂ ψ_good ψ_good = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψg_norm]; norm_num
  have hψb_self : inner ℂ ψ_bad ψ_bad = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψb_norm]; norm_num
  have hφ0_decomp : φ0 = (Real.sin θ : ℂ) • ψ_good + (Real.cos θ : ℂ) • ψ_bad := by
    rw [hsinθ, hcosθ]
    change φ0 = (‖φ_good‖ : ℂ) • (((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good) +
      (‖φ_bad‖ : ℂ) • (((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad)
    rw [smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      mul_one_div_cancel hgp.ne', mul_one_div_cancel hbp.ne', Complex.ofReal_one, one_smul, one_smul]
    ext z; dsimp [φ_good, φ_bad]; split_ifs <;> simp
  have hSg_good : act S_good ψ_good = -ψ_good := by
    ext z
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_diagonal, ψ_good, φ_good, WithLp.ofLp_smul,
      WithLp.ofLp_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, S_good]
    split_ifs <;> ring
  have hSg_bad : act S_good ψ_bad = ψ_bad := by
    ext z
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_diagonal, ψ_bad, φ_bad, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, S_good]
    split_ifs <;> ring
  have hS0_act : ∀ v : EuclideanSpace ℂ (Qubits W),
      act (A * S_zero * star A) v = v - (2 * inner ℂ φ0 v) • φ0 := by
    intro v
    have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hA
    have hS0 : ∀ u : EuclideanSpace ℂ (Qubits W),
        act S_zero u = u - (2 * inner ℂ (zeroKet W) u) • zeroKet W := by
      intro u
      ext z
      have hz0 : inner ℂ (zeroKet W) u = u (fun _ => false) := by
        dsimp [zeroKet]; exact inner_ket_left _ u
      rw [hz0]
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec_diagonal, S_zero, WithLp.ofLp_sub,
        WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zeroKet, ket, PiLp.single_apply]
      split_ifs with h
      · subst h; ring
      · simp
    rw [act_mul, act_mul, hS0 (act (star A) v), act_sub, act_smul, ← act_mul, hAA, act_one_vec]
    have hin : inner ℂ (zeroKet W) (act (star A) v) = inner ℂ φ0 v := by
      dsimp [φ0]
      rw [inner_act_star]
    rw [hin]
  have hG_step : ∀ α : ℝ,
      act G ((Real.sin α : ℂ) • ψ_good + (Real.cos α : ℂ) • ψ_bad) =
        -((Real.sin (α + 2 * θ) : ℂ) • ψ_good + (Real.cos (α + 2 * θ) : ℂ) • ψ_bad) := by
    intro α
    dsimp only [G]
    rw [act_mul, act_add, act_smul (c := (Real.sin α : ℂ)), act_smul (c := (Real.cos α : ℂ)),
      hSg_good, hSg_bad, smul_neg, hS0_act]
    have hin_step : inner ℂ φ0 (-((Real.sin α : ℂ) • ψ_good) + (Real.cos α : ℂ) • ψ_bad) =
        (Real.cos (α + θ) : ℂ) := by
      rw [hφ0_decomp, inner_add_left, inner_add_right, inner_add_right,
        inner_neg_right, inner_neg_right,
        inner_smul_left (x := ψ_good) (r := (Real.sin θ : ℂ)),
        inner_smul_left (x := ψ_good) (r := (Real.sin θ : ℂ)),
        inner_smul_left (x := ψ_bad) (r := (Real.cos θ : ℂ)),
        inner_smul_left (x := ψ_bad) (r := (Real.cos θ : ℂ)),
        inner_smul_right (y := ψ_good) (r := (Real.sin α : ℂ)),
        inner_smul_right (y := ψ_bad) (r := (Real.cos α : ℂ)),
        inner_smul_right (y := ψ_good) (r := (Real.sin α : ℂ)),
        inner_smul_right (y := ψ_bad) (r := (Real.cos α : ℂ)),
        hψg_self, hψb_self, hψg_ψb, hψb_ψg,
        Complex.conj_ofReal, Complex.conj_ofReal]
      have hreal : -(Real.sin θ * Real.sin α) + Real.cos θ * Real.cos α = Real.cos (α + θ) := by
        rw [Real.cos_add]; ring
      have hcc := congrArg (Complex.ofReal) hreal
      simpa [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg] using hcc
    rw [hin_step, hφ0_decomp]
    have hcoeff1 : -(Real.sin α : ℂ) - 2 * (Real.cos (α + θ) : ℂ) * (Real.sin θ : ℂ) =
        -(Real.sin (α + 2 * θ) : ℂ) := by
      have hr : -Real.sin α - 2 * Real.cos (α + θ) * Real.sin θ = -Real.sin (α + 2 * θ) := by
        rw [show α + 2 * θ = (α + θ) + θ by ring]
        simp only [Real.sin_add, Real.cos_add]
        linear_combination Real.sin α * Real.sin_sq_add_cos_sq θ
      exact_mod_cast hr
    have hcoeff2 : (Real.cos α : ℂ) - 2 * (Real.cos (α + θ) : ℂ) * (Real.cos θ : ℂ) =
        -(Real.cos (α + 2 * θ) : ℂ) := by
      have hr : Real.cos α - 2 * Real.cos (α + θ) * Real.cos θ = -Real.cos (α + 2 * θ) := by
        rw [show α + 2 * θ = (α + θ) + θ by ring]
        simp only [Real.cos_add, Real.sin_add]
        linear_combination -Real.cos α * Real.sin_sq_add_cos_sq θ
      exact_mod_cast hr
    ext z
    simp only [WithLp.ofLp_sub, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_neg, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (ψ_good z) * hcoeff1 + (ψ_bad z) * hcoeff2
  induction t with
  | zero =>
    simp only [pow_zero, act_one_vec, Nat.cast_zero, mul_zero, zero_add, one_mul, one_smul]
    exact hφ0_decomp
  | succ t ih =>
    rw [pow_succ', act_mul, ih, act_smul, hG_step ((2 * (t : ℝ) + 1) * θ)]
    have hang : (2 * (t : ℝ) + 1) * θ + 2 * θ = (2 * ((t + 1 : ℕ) : ℝ) + 1) * θ := by
      push_cast; ring
    rw [hang, smul_neg, ← neg_smul, pow_succ]
    congr 1; ring

def skipFlagEmb (W anc : ℕ) : Fin (W + anc) ↪ Fin (W + 1 + anc) where
  toFun i := if i.1 < W then ⟨i.1, by omega⟩ else ⟨i.1 + 1, by omega⟩
  inj' a b hab := by
    have habv := congrArg Fin.val hab
    dsimp at habv
    ext
    by_cases ha : a.1 < W <;> by_cases hb : b.1 < W
    · simp only [ha, hb, ↓reduceIte, Fin.val_mk] at habv; omega
    · simp only [ha, hb, ↓reduceIte, Fin.val_mk] at habv; omega
    · simp only [ha, hb, ↓reduceIte, Fin.val_mk] at habv; omega
    · simp only [ha, hb, ↓reduceIte, Fin.val_mk] at habv; omega

lemma skipFlagEmb_lt {W anc : ℕ} (j : Fin (W + anc)) (hj : j.1 < W) :
    skipFlagEmb W anc j = ⟨j.1, by omega⟩ := by
  ext
  change (if j.1 < W then (⟨j.1, by omega⟩ : Fin (W + 1 + anc)) else ⟨j.1 + 1, by omega⟩).1 = j.1
  simp [hj]

lemma skipFlagEmb_ge {W anc : ℕ} (j : Fin (W + anc)) (hj : W ≤ j.1) :
    skipFlagEmb W anc j = ⟨j.1 + 1, by omega⟩ := by
  ext
  have hnot : ¬ j.1 < W := by omega
  change (if j.1 < W then (⟨j.1, by omega⟩ : Fin (W + 1 + anc)) else ⟨j.1 + 1, by omega⟩).1 = j.1 + 1
  simp [hnot]

def singleCopyGroverCirc {W anc_g anc_z anc_m : ℕ}
    (c_good : Circuit gates12 (W + anc_g))
    (c_zero : Circuit gates12 (W + anc_z))
    (c_mark : Circuit gates12 ((W + 1) + anc_m))
    (t : ℕ) :
    OracleCircuit gates12 (fun _ : Fin 1 => W) (W + 1 + max anc_g (max anc_z anc_m)) :=
  let anc := max anc_g (max anc_z anc_m)
  let embW : Fin W ↪ Fin (W + anc) := Fin.castAddEmb anc
  let c_good' : Circuit gates12 (W + anc) :=
    embedCircuit (padFalseEmb W anc_g anc (le_max_left _ _)) c_good
  let c_zero' : Circuit gates12 (W + anc) :=
    embedCircuit (padFalseEmb W anc_z anc (le_trans (le_max_left _ _) (le_max_right _ _))) c_zero
  let c_mark' : Circuit gates12 ((W + 1) + anc) :=
    embedCircuit (padFalseEmb (W + 1) anc_m anc (le_trans (le_max_right _ _) (le_max_right _ _))) c_mark
  let stepG : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    (c_good'.map OracleStep.gate) ++ [OracleStep.query (0 : Fin 1) true none embW (by simp)] ++
      (c_zero'.map OracleStep.gate) ++ [OracleStep.query (0 : Fin 1) false none embW (by simp)]
  let grov : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    [OracleStep.query (0 : Fin 1) false none embW (by simp)] ++ (List.replicate t stepG).flatten
  embedOracleCircuit (skipFlagEmb W anc) grov ++ (c_mark'.map OracleStep.gate)

lemma singleCopyGroverCirc_uncontrolled {W anc_g anc_z anc_m : ℕ}
    (c_good : Circuit gates12 (W + anc_g))
    (c_zero : Circuit gates12 (W + anc_z))
    (c_mark : Circuit gates12 ((W + 1) + anc_m))
    (t : ℕ) :
    Uncontrolled (singleCopyGroverCirc c_good c_zero c_mark t) := by
  intro st hst
  dsimp only [singleCopyGroverCirc] at hst
  rcases List.mem_append.mp hst with h1 | h2
  · refine embedOracleCircuit_uncontrolled _ (fun s hs => ?_) st h1
    rcases List.mem_append.mp hs with hs1 | hs2
    · rw [List.mem_singleton] at hs1; subst hs1; trivial
    · rw [List.mem_flatten] at hs2
      rcases hs2 with ⟨l, hl, hsl⟩
      rw [List.mem_replicate] at hl
      rcases hl with ⟨_, rfl⟩
      rcases List.mem_append.mp hsl with hsl1 | hsl2
      · rcases List.mem_append.mp hsl1 with hsl1a | hsl1b
        · rcases List.mem_append.mp hsl1a with hA | hB
          · exact uncontrolled_lift _ s hA
          · rw [List.mem_singleton] at hB; subst hB; trivial
        · exact uncontrolled_lift _ s hsl1b
      · rw [List.mem_singleton] at hsl2; subst hsl2; trivial
  · exact uncontrolled_lift _ st h2

lemma singleCopyGroverCirc_queryCount {W anc_g anc_z anc_m : ℕ}
    (c_good : Circuit gates12 (W + anc_g))
    (c_zero : Circuit gates12 (W + anc_z))
    (c_mark : Circuit gates12 ((W + 1) + anc_m))
    (t : ℕ) :
    (singleCopyGroverCirc c_good c_zero c_mark t).queryCount 0 = 2 * t + 1 := by
  dsimp only [singleCopyGroverCirc]
  rw [oracleCircuit_queryCount_append, oracleCircuit_queryCount_lift, add_zero,
    embedOracleCircuit_queryCount, oracleCircuit_queryCount_append]
  let anc := max anc_g (max anc_z anc_m)
  let embW : Fin W ↪ Fin (W + anc) := Fin.castAddEmb anc
  let stepG : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    ((embedCircuit (padFalseEmb W anc_g anc (le_max_left _ _)) c_good).map OracleStep.gate) ++
      [OracleStep.query (0 : Fin 1) true none embW (by simp)] ++
      ((embedCircuit (padFalseEmb W anc_z anc (le_trans (le_max_left _ _) (le_max_right _ _))) c_zero).map OracleStep.gate) ++
      [OracleStep.query (0 : Fin 1) false none embW (by simp)]
  have h1 : OracleCircuit.queryCount ([OracleStep.query (0 : Fin 1) false none
      embW (by simp)] : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) 0 = 1 := by
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
  have hstep : OracleCircuit.queryCount stepG 0 = 2 := by
    dsimp only [stepG]
    simp only [oracleCircuit_queryCount_append, oracleCircuit_queryCount_lift]
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
  have hrep : ∀ k : ℕ,
      OracleCircuit.queryCount ((List.replicate k stepG).flatten :
        OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) 0 = 2 * k := by
    intro k
    induction k with
    | zero => simp [OracleCircuit.queryCount]
    | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, oracleCircuit_queryCount_append, hstep, ih]
      omega
  rw [h1, hrep t]
  omega

lemma singleCopyGroverCirc_gateCount {W anc_g anc_z anc_m : ℕ}
    (c_good : Circuit gates12 (W + anc_g))
    (c_zero : Circuit gates12 (W + anc_z))
    (c_mark : Circuit gates12 ((W + 1) + anc_m))
    (t : ℕ) :
    (singleCopyGroverCirc c_good c_zero c_mark t).gateCount =
      t * (c_good.length + c_zero.length) + c_mark.length := by
  dsimp only [singleCopyGroverCirc]
  rw [oracleCircuit_gateCount_append, oracleCircuit_gateCount_lift, embedCircuit_length,
    embedOracleCircuit_gateCount, oracleCircuit_gateCount_append]
  let anc := max anc_g (max anc_z anc_m)
  let embW : Fin W ↪ Fin (W + anc) := Fin.castAddEmb anc
  let stepG : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    ((embedCircuit (padFalseEmb W anc_g anc (le_max_left _ _)) c_good).map OracleStep.gate) ++
      [OracleStep.query (0 : Fin 1) true none embW (by simp)] ++
      ((embedCircuit (padFalseEmb W anc_z anc (le_trans (le_max_left _ _) (le_max_right _ _))) c_zero).map OracleStep.gate) ++
      [OracleStep.query (0 : Fin 1) false none embW (by simp)]
  have h1 : OracleCircuit.gateCount ([OracleStep.query (0 : Fin 1) false none
      embW (by simp)] : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) = 0 := by
    simp [OracleCircuit.gateCount]
  have hstep : OracleCircuit.gateCount stepG = c_good.length + c_zero.length := by
    dsimp only [stepG]
    simp only [oracleCircuit_gateCount_append, oracleCircuit_gateCount_lift, embedCircuit_length]
    simp [OracleCircuit.gateCount]
  have hrep : ∀ k : ℕ,
      OracleCircuit.gateCount ((List.replicate k stepG).flatten :
        OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) = k * (c_good.length + c_zero.length) := by
    intro k
    induction k with
    | zero => simp [OracleCircuit.gateCount]
    | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, oracleCircuit_gateCount_append, hstep, ih]
      ring
  rw [h1, zero_add, hrep t]

lemma singleCopyGroverCirc_act {W anc_g anc_z anc_m : ℕ}
    (good : Qubits W → Bool)
    (c_good : Circuit gates12 (W + anc_g))
    (c_zero : Circuit gates12 (W + anc_z))
    (c_mark : Circuit gates12 ((W + 1) + anc_m))
    (hgood : ∀ z : Qubits W,
      act c_good.unitary (ket (padFalse W anc_g z)) =
        (if good z then (-1 : ℂ) else 1) • ket (padFalse W anc_g z))
    (hzero : ∀ z : Qubits W,
      act c_zero.unitary (ket (padFalse W anc_z z)) =
        (if z = (fun _ => false) then (-1 : ℂ) else 1) • ket (padFalse W anc_z z))
    (hmark : ∀ (z : Qubits W) (b : Bool),
      act c_mark.unitary (ket (padFalse (W + 1) anc_m (Fin.snoc z b))) =
        ket (padFalse (W + 1) anc_m (Fin.snoc z (xor b (good z)))))
    (t : ℕ)
    (A : Matrix (Qubits W) (Qubits W) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits W) ℂ) :
    let φ0 := act A (zeroKet W)
    let φ_good : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then φ0 z else 0
    let φ_bad : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then 0 else φ0 z
    0 < ‖φ_good‖ → 0 < ‖φ_bad‖ →
    let θ := Real.arcsin ‖φ_good‖
    let ψ_good := ((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good
    let ψ_bad := ((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad
    let anc := max anc_g (max anc_z anc_m)
    act ((singleCopyGroverCirc c_good c_zero c_mark t).unitary fun _ => A) (zeroKet (W + 1 + anc)) =
      ∑ z : Qubits W,
        ((-1 : ℂ) ^ t * (if good z then (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_good z
                          else (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_bad z)) •
          ket (padFalse (W + 1) anc (Fin.snoc z (good z))) := by
  intro φ0 φ_good φ_bad hgp hbp θ ψ_good ψ_bad anc
  let embW : Fin W ↪ Fin (W + anc) := Fin.castAddEmb anc
  let c_good' : Circuit gates12 (W + anc) :=
    embedCircuit (padFalseEmb W anc_g anc (le_max_left _ _)) c_good
  let c_zero' : Circuit gates12 (W + anc) :=
    embedCircuit (padFalseEmb W anc_z anc (le_trans (le_max_left _ _) (le_max_right _ _))) c_zero
  let c_mark' : Circuit gates12 ((W + 1) + anc) :=
    embedCircuit (padFalseEmb (W + 1) anc_m anc (le_trans (le_max_right _ _) (le_max_right _ _))) c_mark
  let S_good : Matrix (Qubits W) (Qubits W) ℂ :=
    Matrix.diagonal fun z => if good z then (-1 : ℂ) else 1
  let S_zero : Matrix (Qubits W) (Qubits W) ℂ :=
    Matrix.diagonal fun z => if z = (fun _ => false) then (-1 : ℂ) else 1
  let G := A * S_zero * star A * S_good
  have hgood' : ∀ x : Qubits W, act c_good'.unitary (ket (padFalse W anc x)) =
      (if good x then (-1 : ℂ) else 1) • ket (padFalse W anc x) :=
    padFalse_circuit_act (le_max_left _ _) c_good _ id hgood
  have hzero' : ∀ x : Qubits W, act c_zero'.unitary (ket (padFalse W anc x)) =
      (if x = (fun _ => false) then (-1 : ℂ) else 1) • ket (padFalse W anc x) :=
    padFalse_circuit_act (le_trans (le_max_left _ _) (le_max_right _ _)) c_zero _ id hzero
  have hmark' : ∀ (z : Qubits W) (b : Bool), act c_mark'.unitary (ket (padFalse (W + 1) anc (Fin.snoc z b))) =
      ket (padFalse (W + 1) anc (Fin.snoc z (xor b (good z)))) := by
    intro z b
    have hm := padFalse_circuit_act (anc₂ := anc)
      (le_trans (le_max_right anc_z anc_m) (le_max_right anc_g (max anc_z anc_m))) c_mark
      (fun _ => (1 : ℂ))
      (fun x' => Fin.snoc (fun i : Fin W => x' i.castSucc) (xor (x' (Fin.last W)) (good (fun i : Fin W => x' i.castSucc))))
      (fun x' => by
        have hx' : x' = Fin.snoc (fun i : Fin W => x' i.castSucc) (x' (Fin.last W)) := by
          funext w; refine Fin.lastCases (by simp) (fun i => by simp) w
        conv_lhs => rw [hx']
        rw [one_smul]
        have hres := hmark (fun i : Fin W => x' i.castSucc) (x' (Fin.last W))
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using hres)
      (Fin.snoc z b)
    simpa [Fin.snoc_castSucc, Fin.snoc_last] using hm
  let stepG : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    (c_good'.map OracleStep.gate) ++ [OracleStep.query (0 : Fin 1) true none embW (by simp)] ++
      (c_zero'.map OracleStep.gate) ++ [OracleStep.query (0 : Fin 1) false none embW (by simp)]
  have hstep_act : ∀ φ : EuclideanSpace ℂ (Qubits W),
      act (stepG.unitary fun _ => A) (liftClean W anc φ) = liftClean W anc (act G φ) := by
    intro φ
    have hq_adj : OracleCircuit.unitary ([OracleStep.query (0 : Fin 1) true none embW (by simp)] :
        OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) (fun _ => A) =
        embedOp (star A) embW := by
      simp [OracleCircuit.unitary, OracleStep.mat]
    have hq_fwd : OracleCircuit.unitary ([OracleStep.query (0 : Fin 1) false none embW (by simp)] :
        OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) (fun _ => A) =
        embedOp A embW := by
      simp [OracleCircuit.unitary, OracleStep.mat]
    have hunit : stepG.unitary (fun _ => A) =
        embedOp A embW * c_zero'.unitary * embedOp (star A) embW * c_good'.unitary := by
      dsimp only [stepG]
      rw [oracleCircuit_unitary_append, oracleCircuit_unitary_append, oracleCircuit_unitary_append,
        oracleCircuit_unitary_lift, oracleCircuit_unitary_lift, hq_adj, hq_fwd]
      simp [Matrix.mul_assoc]
    rw [hunit, act_mul, act_mul, act_mul,
      act_clean_diag_liftClean c_good' _ hgood' φ,
      act_embedOp_liftClean (star A),
      act_clean_diag_liftClean c_zero' _ hzero',
      act_embedOp_liftClean A]
    congr 1
    simp only [G, act_mul]
    rfl
  let grov : OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc) :=
    [OracleStep.query (0 : Fin 1) false none embW (by simp)] ++ (List.replicate t stepG).flatten
  have hgrov_un : Uncontrolled grov := by
    intro s hs
    rcases List.mem_append.mp hs with hs1 | hs2
    · rw [List.mem_singleton] at hs1; subst hs1; trivial
    · rw [List.mem_flatten] at hs2
      rcases hs2 with ⟨l, hl, hsl⟩
      rw [List.mem_replicate] at hl
      rcases hl with ⟨_, rfl⟩
      rcases List.mem_append.mp hsl with hsl1 | hsl2
      · rcases List.mem_append.mp hsl1 with hsl1a | hsl1b
        · rcases List.mem_append.mp hsl1a with hA' | hB'
          · exact uncontrolled_lift _ s hA'
          · rw [List.mem_singleton] at hB'; subst hB'; trivial
        · exact uncontrolled_lift _ s hsl1b
      · rw [List.mem_singleton] at hsl2; subst hsl2; trivial
  have hrep_act : ∀ k : ℕ, ∀ φ : EuclideanSpace ℂ (Qubits W),
      act (OracleCircuit.unitary (List.replicate k stepG).flatten (fun _ => A))
        (liftClean W anc φ) = liftClean W anc (act (G ^ k) φ) := by
    intro k
    induction k with
    | zero =>
      intro φ
      rw [List.replicate_zero, List.flatten_nil]
      simp only [OracleCircuit.unitary, List.map_nil, List.reverse_nil, List.prod_nil,
        pow_zero, act_one_vec]
    | succ k ih =>
      intro φ
      rw [List.replicate_succ, List.flatten_cons, oracleCircuit_unitary_append, act_mul,
        hstep_act, ih, ← act_mul, ← pow_succ]
  have hgrov_act : act (grov.unitary fun _ => A) (zeroKet (W + anc)) =
      liftClean W anc (act (G ^ t) φ0) := by
    dsimp only [grov]
    rw [oracleCircuit_unitary_append, act_mul, ← liftClean_zeroKet W anc]
    have hq0 : act (OracleCircuit.unitary ([OracleStep.query (0 : Fin 1) false none embW (by simp)] :
        OracleCircuit gates12 (fun _ : Fin 1 => W) (W + anc)) (fun _ => A))
        (liftClean W anc (zeroKet W)) = liftClean W anc φ0 := by
      simp only [OracleCircuit.unitary, List.map_singleton, List.reverse_singleton,
        List.prod_singleton, OracleStep.mat, Bool.false_eq_true, ↓reduceIte]
      exact act_embedOp_liftClean A (zeroKet W)
    rw [hq0, hrep_act t φ0]
  have hrot := grover_iter_2d A hA good t hgp hbp
  have hsupp_g : ∀ z : Qubits W, ¬ good z → ψ_good z = 0 := fun z hz => by
    dsimp [ψ_good, φ_good]; simp [hz]
  have hsupp_b : ∀ z : Qubits W, good z → ψ_bad z = 0 := fun z hz => by
    dsimp [ψ_bad, φ_bad]; simp [hz]
  have hgrov_vec : act (grov.unitary fun _ => A) (zeroKet (W + anc)) =
      ∑ z : Qubits W,
        ((-1 : ℂ) ^ t * (if good z then (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_good z
                          else (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_bad z)) •
          ket (padFalse W anc z) := by
    rw [hgrov_act]
    exact (congrArg (liftClean W anc) hrot).trans
      (liftClean_good_bad good ψ_good ψ_bad hsupp_g hsupp_b ((-1 : ℂ) ^ t)
        (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ))
  dsimp only [singleCopyGroverCirc]
  rw [oracleCircuit_unitary_append, oracleCircuit_unitary_lift, act_mul,
    embedOracleCircuit_unitary_of_uncontrolled (skipFlagEmb W anc) hgrov_un]
  have hemb_act : act (embedOp (grov.unitary fun _ => A) (skipFlagEmb W anc))
      (zeroKet (W + 1 + anc)) =
      ∑ z : Qubits W,
        ((-1 : ℂ) ^ t * (if good z then (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_good z
                          else (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_bad z)) •
          ket (padFalse (W + 1) anc (Fin.snoc z false)) := by
    dsimp [zeroKet]
    ext y
    rw [act_embedOp_apply]
    have hz_in : ∀ u : Qubits (W + anc),
        (ket (fun _ : Fin (W + 1 + anc) => false)) (updateOn (skipFlagEmb W anc) y u) =
          if (∀ i : Fin (W + 1 + anc), i ∉ Set.range (skipFlagEmb W anc) → y i = false) ∧
              u = (fun _ => false) then 1 else 0 := by
      intro u
      simp only [ket, PiLp.single_apply]
      by_cases hcond : (∀ i : Fin (W + 1 + anc), i ∉ Set.range (skipFlagEmb W anc) → y i = false) ∧
          u = (fun _ => false)
      · rw [if_pos hcond, if_pos]
        funext i
        by_cases hi : i ∈ Set.range (skipFlagEmb W anc)
        · obtain ⟨j, rfl⟩ := hi
          rw [updateOn_apply, hcond.2]
        · rw [updateOn_off _ _ _ hi, hcond.1 i hi]
      · rw [if_neg hcond, if_neg]
        intro heq
        apply hcond
        refine ⟨fun i hi => ?_, ?_⟩
        · simpa [updateOn_off _ _ _ hi] using congrFun heq i
        · funext j
          have hj := congrFun heq (skipFlagEmb W anc j)
          rw [updateOn_apply] at hj
          exact hj
    have hnot_flag : ∀ i : Fin (W + 1 + anc),
        i ∉ Set.range (skipFlagEmb W anc) ↔ i.1 = W := by
      intro i
      constructor
      · intro hi
        by_contra hne
        apply hi
        by_cases hlt : i.1 < W
        · refine ⟨⟨i.1, by omega⟩, Fin.ext ?_⟩
          rw [skipFlagEmb_lt _ hlt]
        · refine ⟨⟨i.1 - 1, by omega⟩, Fin.ext ?_⟩
          rw [skipFlagEmb_ge ⟨i.1 - 1, by omega⟩ (by dsimp; omega)]; dsimp; omega
      · intro hi ⟨j, hj⟩
        have hjv := congrArg Fin.val hj
        change (if j.1 < W then (⟨j.1, by omega⟩ : Fin (W + 1 + anc)) else ⟨j.1 + 1, by omega⟩).1 = i.1 at hjv
        split_ifs at hjv <;> simp only at hjv <;> omega
    have hsum_single : (∑ u : Qubits (W + anc),
          (grov.unitary fun _ => A) (y ∘ skipFlagEmb W anc) u *
            (ket (fun _ : Fin (W + 1 + anc) => false)) (updateOn (skipFlagEmb W anc) y u)) =
        if y ⟨W, by omega⟩ = false then
          (act (grov.unitary fun _ => A) (zeroKet (W + anc))) (y ∘ skipFlagEmb W anc) else 0 := by
      simp_rw [hz_in]
      by_cases hyW : y ⟨W, by omega⟩ = false
      · rw [if_pos hyW]
        have hout : ∀ i : Fin (W + 1 + anc), i ∉ Set.range (skipFlagEmb W anc) → y i = false := by
          intro i hi
          have hiW := (hnot_flag i).mp hi
          have heq : i = ⟨W, by omega⟩ := Fin.ext hiW
          rw [heq, hyW]
        rw [Finset.sum_eq_single (fun _ => false)]
        · rw [if_pos ⟨hout, rfl⟩, mul_one]
          simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, zeroKet, ket, PiLp.single_apply]
          rw [Finset.sum_eq_single (fun _ => false)]
          · simp
          · intro u _ hu; simp [hu]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro u _ hu
          have hne : ¬ ((∀ i, i ∉ Set.range (skipFlagEmb W anc) → y i = false) ∧ u = fun _ => false) :=
            fun h => hu h.2
          rw [if_neg hne, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hyW]
        refine Finset.sum_eq_zero fun u _ => ?_
        have hne : ¬ ((∀ i, i ∉ Set.range (skipFlagEmb W anc) → y i = false) ∧ u = fun _ => false) := by
          intro h
          apply hyW
          exact h.1 ⟨W, by omega⟩ ((hnot_flag ⟨W, by omega⟩).mpr rfl)
        rw [if_neg hne, mul_zero]
    rw [hsum_single, hgrov_vec]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ket, PiLp.single_apply]
    by_cases hyW : y ⟨W, by omega⟩ = false
    · rw [if_pos hyW]
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      have heq : (y ∘ skipFlagEmb W anc = padFalse W anc z) ↔
          (y = padFalse (W + 1) anc (Fin.snoc z false)) := by
        constructor
        · intro h
          funext i
          by_cases hlt : i.1 < W
          · have hi1 : i = skipFlagEmb W anc ⟨i.1, by omega⟩ := Fin.ext (by rw [skipFlagEmb_lt _ hlt])
            have hi2 : i = Fin.castAdd anc (Fin.castSucc ⟨i.1, hlt⟩) := Fin.ext rfl
            calc y i = y (skipFlagEmb W anc ⟨i.1, by omega⟩) := by rw [← hi1]
              _ = (y ∘ skipFlagEmb W anc) ⟨i.1, by omega⟩ := rfl
              _ = padFalse W anc z ⟨i.1, by omega⟩ := congrFun h _
              _ = z ⟨i.1, hlt⟩ := by
                  have h3 : (⟨i.1, by omega⟩ : Fin (W + anc)) = Fin.castAdd anc ⟨i.1, hlt⟩ := rfl
                  rw [h3, padFalse_castAdd]
              _ = padFalse (W + 1) anc (Fin.snoc z false) i := by
                  calc z ⟨i.1, hlt⟩
                      = padFalse (W + 1) anc (Fin.snoc z false) (Fin.castAdd anc (Fin.castSucc ⟨i.1, hlt⟩)) := by
                          rw [padFalse_castAdd, Fin.snoc_castSucc]
                    _ = padFalse (W + 1) anc (Fin.snoc z false) i := congrArg _ hi2.symm
          · by_cases heqW : i.1 = W
            · have hi1 : i = ⟨W, by omega⟩ := Fin.ext heqW
              have hi2 : i = Fin.castAdd anc (Fin.last W) := Fin.ext (by simp [heqW])
              calc y i = y ⟨W, by omega⟩ := congrArg y hi1
                _ = false := hyW
                _ = padFalse (W + 1) anc (Fin.snoc z false) i := by
                    calc false
                        = padFalse (W + 1) anc (Fin.snoc z false) (Fin.castAdd anc (Fin.last W)) := by
                            rw [padFalse_castAdd, Fin.snoc_last]
                      _ = padFalse (W + 1) anc (Fin.snoc z false) i := congrArg _ hi2.symm
            · have hgt : W < i.1 := by omega
              have hi1 : i = skipFlagEmb W anc ⟨i.1 - 1, by omega⟩ :=
                Fin.ext (by rw [skipFlagEmb_ge ⟨i.1 - 1, by omega⟩ (by dsimp; omega)]; dsimp; omega)
              have hi2 : i = Fin.natAdd (W + 1) ⟨i.1 - (W + 1), by omega⟩ := Fin.ext (by simp; omega)
              have hpad : (⟨i.1 - 1, by omega⟩ : Fin (W + anc)) = Fin.natAdd W ⟨i.1 - (W + 1), by omega⟩ :=
                Fin.ext (by simp; omega)
              calc y i = y (skipFlagEmb W anc ⟨i.1 - 1, by omega⟩) := congrArg y hi1
                _ = (y ∘ skipFlagEmb W anc) ⟨i.1 - 1, by omega⟩ := rfl
                _ = padFalse W anc z ⟨i.1 - 1, by omega⟩ := congrFun h _
                _ = false := by rw [hpad, padFalse_natAdd]
                _ = padFalse (W + 1) anc (Fin.snoc z false) i := by
                    calc false
                        = padFalse (W + 1) anc (Fin.snoc z false) (Fin.natAdd (W + 1) ⟨i.1 - (W + 1), by omega⟩) :=
                            (padFalse_natAdd (W + 1) anc (Fin.snoc z false) _).symm
                      _ = padFalse (W + 1) anc (Fin.snoc z false) i := congrArg _ hi2.symm
        · intro h
          funext j
          rw [h, Function.comp_apply]
          by_cases hlt : j.1 < W
          · rw [skipFlagEmb_lt _ hlt]
            have hj1 : (⟨j.1, by omega⟩ : Fin (W + 1 + anc)) = Fin.castAdd anc (Fin.castSucc ⟨j.1, hlt⟩) :=
              Fin.ext rfl
            have hj2 : j = Fin.castAdd anc ⟨j.1, hlt⟩ := Fin.ext rfl
            rw [hj1, padFalse_castAdd, Fin.snoc_castSucc]
            calc z ⟨j.1, hlt⟩
                = padFalse W anc z (Fin.castAdd anc ⟨j.1, hlt⟩) := (padFalse_castAdd W anc z _).symm
              _ = padFalse W anc z j := congrArg (padFalse W anc z) hj2.symm
          · rw [skipFlagEmb_ge _ (by omega)]
            have hj1 : (⟨j.1 + 1, by omega⟩ : Fin (W + 1 + anc)) = Fin.natAdd (W + 1) ⟨j.1 - W, by omega⟩ :=
              Fin.ext (by simp; omega)
            have hj2 : j = Fin.natAdd W ⟨j.1 - W, by omega⟩ := Fin.ext (by simp; omega)
            rw [hj1, padFalse_natAdd]
            exact (by rw [hj2, padFalse_natAdd] : false = padFalse W anc z j)
      by_cases h1 : y ∘ skipFlagEmb W anc = padFalse W anc z
      · rw [if_pos h1, if_pos (heq.mp h1)]
      · rw [if_neg h1, if_neg (fun h => h1 (heq.mpr h))]
    · rw [if_neg hyW]
      symm
      refine Finset.sum_eq_zero fun z _ => ?_
      have hne : y ≠ padFalse (W + 1) anc (Fin.snoc z false) := fun h => by
        apply hyW
        have h1 : (⟨W, by omega⟩ : Fin (W + 1 + anc)) = Fin.castAdd anc (Fin.last W) := Fin.ext rfl
        rw [h, h1, padFalse_castAdd, Fin.snoc_last]
      rw [if_neg hne, mul_zero]
  rw [hemb_act, act_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [act_smul]
  have hm := hmark' z false
  simp only [Bool.false_xor] at hm
  rw [hm]

/-! ### 4. Parallel `R`-Copy Tensor Evolution, `firstHitSwap`, and `n = 0` Case -/

/-- Extra ancilla/copy wire count `e` for `R` disjoint copies + `anc_sw` clean swap ancillas. -/
def e53 (R m_reg a anc_copy anc_sw : ℕ) : ℕ :=
  (R - 1) * m_reg + R + anc_sw + R * (1 + a + anc_copy)

lemma e53_total_eq {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) :
    m_reg + e53 R m_reg a anc_copy anc_sw =
      R * m_reg + R + anc_sw + R * (1 + a + anc_copy) := by
  dsimp only [e53]
  have h1 : m_reg + (R - 1) * m_reg = R * m_reg := by
    calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
      _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
      _ = R * m_reg := by congr 1; omega
  omega

/-- Flag embedding `Fin R ↪ Fin (e53 R m_reg a anc_copy anc_sw)`. -/
def flag53 (R m_reg a anc_copy anc_sw : ℕ) :
    Fin R ↪ Fin (e53 R m_reg a anc_copy anc_sw) where
  toFun j := ⟨(R - 1) * m_reg + j.1, by dsimp [e53]; omega⟩
  inj' a b h := by
    ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

/-- Concrete partition equivalence of `m_reg + e53` wires into `R` disjoint single-copy blocks
of size `(m_reg + 1 + a) + 1 + anc_copy` plus `anc_sw` clean swap ancillas. -/
def wireEquiv53 {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m_reg) :
    Fin (m_reg + e53 R m_reg a anc_copy anc_sw) ≃
      (Fin R × Fin ((m_reg + 1 + a) + 1 + anc_copy)) ⊕ Fin anc_sw :=
  let totalW := m_reg + e53 R m_reg a anc_copy anc_sw
  let M_copy := (m_reg + 1 + a) + 1 + anc_copy
  let W := m_reg + 1 + a
  let m_tail := 1 + a + anc_copy
  have htot : totalW = R * m_reg + R + anc_sw + R * m_tail := e53_total_eq hR
  have hmt : 1 ≤ m_tail := by dsimp [m_tail]; omega
  { toFun := fun w =>
      if h1 : w.1 < R * m_reg then
        Sum.inl (⟨w.1 / m_reg, (Nat.div_lt_iff_lt_mul hm).mpr h1⟩,
          ⟨w.1 % m_reg, lt_of_lt_of_le (Nat.mod_lt w.1 hm) (by omega)⟩)
      else if h2 : w.1 < R * m_reg + R then
        Sum.inl (⟨w.1 - R * m_reg, by omega⟩, ⟨W, by dsimp [W]; omega⟩)
      else if h3 : w.1 < R * m_reg + R + anc_sw then
        Sum.inr ⟨w.1 - (R * m_reg + R), by omega⟩
      else
        let off := w.1 - (R * m_reg + R + anc_sw)
        let j : Fin R := ⟨off / m_tail, (Nat.div_lt_iff_lt_mul hmt).mpr (by
          dsimp [off]; omega)⟩
        let k := off % m_tail
        have hk : k < m_tail := Nat.mod_lt off hmt
        if hk1 : k < 1 + a then
          Sum.inl (j, ⟨m_reg + k, by omega⟩)
        else
          Sum.inl (j, ⟨m_reg + k + 1, by dsimp [m_tail] at hk; omega⟩)
    invFun := fun
      | Sum.inl (j, i) =>
        if hi1 : i.1 < m_reg then
          ⟨j.1 * m_reg + i.1, by
            have hj : j.1 + 1 ≤ R := j.isLt
            have hmul : (j.1 + 1) * m_reg ≤ R * m_reg := Nat.mul_le_mul_right m_reg hj
            have hlt : j.1 * m_reg + i.1 < (j.1 + 1) * m_reg := by
              rw [Nat.add_mul, one_mul]; omega
            omega⟩
        else if hi2 : i.1 < W then
          let k := i.1 - m_reg
          have hk : k < m_tail := by dsimp [k, m_tail, W]; omega
          have hj : j.1 + 1 ≤ R := j.isLt
          have hmul : (j.1 + 1) * m_tail ≤ R * m_tail := Nat.mul_le_mul_right m_tail hj
          have hlt : j.1 * m_tail + k < (j.1 + 1) * m_tail := by
            rw [Nat.add_mul, one_mul]; omega
          ⟨R * m_reg + R + anc_sw + j.1 * m_tail + k, by omega⟩
        else if hi3 : i.1 = W then
          ⟨R * m_reg + j.1, by omega⟩
        else
          let k := i.1 - m_reg - 1
          have hk : k < m_tail := by dsimp [k, m_tail, W, M_copy] at *; omega
          have hj : j.1 + 1 ≤ R := j.isLt
          have hmul : (j.1 + 1) * m_tail ≤ R * m_tail := Nat.mul_le_mul_right m_tail hj
          have hlt : j.1 * m_tail + k < (j.1 + 1) * m_tail := by
            rw [Nat.add_mul, one_mul]; omega
          ⟨R * m_reg + R + anc_sw + j.1 * m_tail + k, by omega⟩
      | Sum.inr l =>
        ⟨R * m_reg + R + l.1, by omega⟩
    left_inv := fun w => by
      dsimp only
      by_cases h1 : w.1 < R * m_reg
      · rw [dif_pos h1]
        dsimp only
        have hi : (w.1 % m_reg) < m_reg := Nat.mod_lt w.1 hm
        rw [dif_pos (show w.1 % m_reg < m_reg from hi)]
        ext; dsimp
        have hdm : m_reg * (w.1 / m_reg) + w.1 % m_reg = w.1 := Nat.div_add_mod w.1 m_reg
        rw [mul_comm] at hdm; exact hdm
      · rw [dif_neg h1]
        by_cases h2 : w.1 < R * m_reg + R
        · rw [dif_pos h2]
          dsimp only
          have hW1 : ¬ (W < m_reg) := by dsimp [W]; omega
          have hW2 : ¬ (W < W) := by omega
          rw [dif_neg hW1, dif_neg hW2, dif_pos rfl]
          ext; dsimp; omega
        · rw [dif_neg h2]
          by_cases h3 : w.1 < R * m_reg + R + anc_sw
          · rw [dif_pos h3]
            ext; dsimp; omega
          · rw [dif_neg h3]
            set off := w.1 - (R * m_reg + R + anc_sw)
            have hk_lt : off % m_tail < m_tail := Nat.mod_lt off hmt
            by_cases hk1 : off % m_tail < 1 + a
            · rw [dif_pos hk1]
              dsimp only
              have ha1 : ¬ (m_reg + off % m_tail < m_reg) := by omega
              have ha2 : m_reg + off % m_tail < W := by dsimp [W]; omega
              rw [dif_neg ha1, dif_pos ha2]
              ext; dsimp
              have hdm : m_tail * (off / m_tail) + off % m_tail = off := Nat.div_add_mod off m_tail
              rw [mul_comm] at hdm
              have hsub : m_reg + off % m_tail - m_reg = off % m_tail := by omega
              rw [hsub]; dsimp [off] at hdm ⊢; omega
            · rw [dif_neg hk1]
              dsimp only
              have ha1 : ¬ (m_reg + off % m_tail + 1 < m_reg) := by omega
              have ha2 : ¬ (m_reg + off % m_tail + 1 < W) := by dsimp [W]; omega
              have ha3 : ¬ (m_reg + off % m_tail + 1 = W) := by dsimp [W]; omega
              rw [dif_neg ha1, dif_neg ha2, dif_neg ha3]
              ext; dsimp
              have hdm : m_tail * (off / m_tail) + off % m_tail = off := Nat.div_add_mod off m_tail
              rw [mul_comm] at hdm
              have hsub : m_reg + off % m_tail + 1 - m_reg - 1 = off % m_tail := by omega
              rw [hsub]; dsimp [off] at hdm ⊢; omega
    right_inv := fun x => by
      rcases x with ⟨j, i⟩ | l
      · dsimp only
        by_cases hi1 : i.1 < m_reg
        · rw [dif_pos hi1]
          have h1 : j.1 * m_reg + i.1 < R * m_reg := by
            have hj : j.1 + 1 ≤ R := j.isLt
            have hmul : (j.1 + 1) * m_reg ≤ R * m_reg := Nat.mul_le_mul_right m_reg hj
            have hlt : j.1 * m_reg + i.1 < (j.1 + 1) * m_reg := by
              rw [Nat.add_mul, one_mul]; omega
            omega
          rw [dif_pos h1]
          have hdiv : (j.1 * m_reg + i.1) / m_reg = j.1 := by
            rw [mul_comm j.1 m_reg, Nat.mul_add_div hm, Nat.div_eq_of_lt hi1, add_zero]
          have hmod : (j.1 * m_reg + i.1) % m_reg = i.1 := by
            rw [mul_comm j.1 m_reg, Nat.mul_add_mod, Nat.mod_eq_of_lt hi1]
          apply congrArg Sum.inl
          ext <;> simp [hdiv, hmod]
        · rw [dif_neg hi1]
          by_cases hi2 : i.1 < W
          · rw [dif_pos hi2]
            have h1 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg) < R * m_reg) := by omega
            have h2 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg) < R * m_reg + R) := by omega
            have h3 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg) < R * m_reg + R + anc_sw) := by omega
            rw [dif_neg h1, dif_neg h2, dif_neg h3]
            have hoff : R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg) - (R * m_reg + R + anc_sw) =
                j.1 * m_tail + (i.1 - m_reg) := by omega
            have hkm : i.1 - m_reg < m_tail := by dsimp [m_tail, W] at *; omega
            have hk1a : i.1 - m_reg < 1 + a := by dsimp [W] at *; omega
            have hdiv : (j.1 * m_tail + (i.1 - m_reg)) / m_tail = j.1 := by
              rw [mul_comm j.1 m_tail, Nat.mul_add_div hmt, Nat.div_eq_of_lt hkm, add_zero]
            have hmod : (j.1 * m_tail + (i.1 - m_reg)) % m_tail = i.1 - m_reg := by
              rw [mul_comm j.1 m_tail, Nat.mul_add_mod, Nat.mod_eq_of_lt hkm]
            dsimp only
            simp_rw [hoff, hdiv, hmod]
            rw [dif_pos hk1a]
            exact congrArg Sum.inl (Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; omega)))
          · rw [dif_neg hi2]
            by_cases hi3 : i.1 = W
            · rw [dif_pos hi3]
              have h1 : ¬ (R * m_reg + j.1 < R * m_reg) := by omega
              have h2 : R * m_reg + j.1 < R * m_reg + R := by omega
              rw [dif_neg h1, dif_pos h2]
              exact congrArg Sum.inl (Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega)))
            · rw [dif_neg hi3]
              have h1 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg - 1) < R * m_reg) := by omega
              have h2 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg - 1) < R * m_reg + R) := by omega
              have h3 : ¬ (R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg - 1) < R * m_reg + R + anc_sw) := by omega
              rw [dif_neg h1, dif_neg h2, dif_neg h3]
              have hoff : R * m_reg + R + anc_sw + j.1 * m_tail + (i.1 - m_reg - 1) - (R * m_reg + R + anc_sw) =
                  j.1 * m_tail + (i.1 - m_reg - 1) := by omega
              have hkm : i.1 - m_reg - 1 < m_tail := by dsimp [m_tail, W, M_copy] at *; omega
              have hk1a : ¬ (i.1 - m_reg - 1 < 1 + a) := by dsimp [W] at *; omega
              have hdiv : (j.1 * m_tail + (i.1 - m_reg - 1)) / m_tail = j.1 := by
                rw [mul_comm j.1 m_tail, Nat.mul_add_div hmt, Nat.div_eq_of_lt hkm, add_zero]
              have hmod : (j.1 * m_tail + (i.1 - m_reg - 1)) % m_tail = i.1 - m_reg - 1 := by
                rw [mul_comm j.1 m_tail, Nat.mul_add_mod, Nat.mod_eq_of_lt hkm]
              dsimp only
              simp_rw [hoff, hdiv, hmod]
              rw [dif_neg hk1a]
              exact congrArg Sum.inl (Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp; omega)))
      · dsimp only
        have h1 : ¬ (R * m_reg + R + l.1 < R * m_reg) := by omega
        have h2 : ¬ (R * m_reg + R + l.1 < R * m_reg + R) := by omega
        have h3 : R * m_reg + R + l.1 < R * m_reg + R + anc_sw := by omega
        rw [dif_neg h1, dif_neg h2, dif_pos h3]
        apply congrArg Sum.inr
        ext; dsimp; omega }

def copyEmb53 {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m_reg) (j : Fin R) :
    Fin ((m_reg + 1 + a) + 1 + anc_copy) ↪ Fin (m_reg + e53 R m_reg a anc_copy anc_sw) where
  toFun i := (wireEquiv53 hR hm).symm (Sum.inl (j, i))
  inj' _ _ h := by
    have h' := (wireEquiv53 hR hm).symm.injective h
    have hp := Sum.inl.inj h'
    exact (Prod.mk.inj hp).2

def swapAncEmb53 {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m_reg) :
    Fin anc_sw ↪ Fin (m_reg + e53 R m_reg a anc_copy anc_sw) where
  toFun l := (wireEquiv53 hR hm).symm (Sum.inr l)
  inj' _ _ h := Sum.inr.inj ((wireEquiv53 hR hm).symm.injective h)

lemma copyEmb53_castAdd0 {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m_reg)
    (i : Fin m_reg) :
    Fin.castAdd (e53 R m_reg a anc_copy anc_sw) i =
      copyEmb53 hR hm ⟨0, hR⟩ ⟨i.1, by omega⟩ := by
  have hi1 : i.1 < m_reg := i.isLt
  ext
  simp only [Fin.val_castAdd, copyEmb53, Function.Embedding.coeFn_mk, wireEquiv53,
    Equiv.coe_fn_symm_mk, hi1, ↓reduceDIte, Fin.val_mk, zero_mul, zero_add]

lemma copyEmb53_flag {R m_reg a anc_copy anc_sw : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m_reg)
    (j : Fin R) :
    Fin.natAdd m_reg (flag53 R m_reg a anc_copy anc_sw j) =
      copyEmb53 hR hm j ⟨m_reg + 1 + a, by omega⟩ := by
  have hW1 : ¬ (m_reg + 1 + a < m_reg) := by omega
  have hW2 : ¬ (m_reg + 1 + a < m_reg + 1 + a) := by omega
  have hfl : (flag53 R m_reg a anc_copy anc_sw j).1 = (R - 1) * m_reg + j.1 := rfl
  ext
  rw [Fin.val_natAdd, hfl]
  simp only [copyEmb53, Function.Embedding.coeFn_mk, wireEquiv53,
    Equiv.coe_fn_symm_mk, hW1, hW2, ↓reduceDIte, Fin.val_mk]
  have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
    calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
      _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
      _ = R * m_reg := by congr 1; omega
  omega

lemma swapAncEmb53_ge (R m_reg a anc_copy anc_sw : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m_reg)
    (l : Fin anc_sw) :
    m_reg ≤ (swapAncEmb53 (a := a) (anc_copy := anc_copy) hR hm l).1 := by
  simp only [swapAncEmb53, Function.Embedding.coeFn_mk, wireEquiv53, Equiv.coe_fn_symm_mk,
    Fin.val_mk]
  have h1 : m_reg ≤ R * m_reg := Nat.le_mul_of_pos_left m_reg hR
  omega

lemma copyEmb53_deg_val (R m_reg a anc_copy anc_sw : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m_reg)
    (j : Fin R) (i : Fin m_reg) :
    (copyEmb53 (a := a) (anc_copy := anc_copy) (anc_sw := anc_sw) hR hm j ⟨i.1, by omega⟩).1 =
      j.1 * m_reg + i.1 := by
  have hi : i.1 < m_reg := i.isLt
  simp only [copyEmb53, Function.Embedding.coeFn_mk, wireEquiv53, Equiv.coe_fn_symm_mk, hi,
    ↓reduceDIte, Fin.val_mk]

/-- Sequential composition of `k ≤ R` disjoint embeddings of `c_copy`. -/
def prefixCopiesCirc {r : ℕ} {a : Fin r → ℕ} {M_copy totalW R : ℕ}
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    (c_copy : OracleCircuit gates12 a M_copy) :
    (k : ℕ) → k ≤ R → OracleCircuit gates12 a totalW
  | 0, _ => []
  | k + 1, hk =>
      prefixCopiesCirc copyEmb c_copy k (Nat.le_of_succ_le hk) ++
        embedOracleCircuit (copyEmb ⟨k, hk⟩) c_copy

lemma prefixCopiesCirc_uncontrolled {r : ℕ} {a : Fin r → ℕ} {M_copy totalW R : ℕ}
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    {c_copy : OracleCircuit gates12 a M_copy} (hc : Uncontrolled c_copy)
    (k : ℕ) (hk : k ≤ R) :
    Uncontrolled (prefixCopiesCirc copyEmb c_copy k hk) := by
  induction k with
  | zero => intro s hs; simp [prefixCopiesCirc] at hs
  | succ k ih =>
    intro s hs
    dsimp [prefixCopiesCirc] at hs
    rcases List.mem_append.mp hs with hs1 | hs2
    · exact ih (Nat.le_of_succ_le hk) s hs1
    · exact embedOracleCircuit_uncontrolled _ hc s hs2

lemma prefixCopiesCirc_queryCount {r : ℕ} {a : Fin r → ℕ} {M_copy totalW R : ℕ}
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    (c_copy : OracleCircuit gates12 a M_copy)
    (k : ℕ) (hk : k ≤ R) (k₀ : Fin r) :
    (prefixCopiesCirc copyEmb c_copy k hk).queryCount k₀ = k * c_copy.queryCount k₀ := by
  induction k with
  | zero => simp [prefixCopiesCirc, OracleCircuit.queryCount]
  | succ k ih =>
    dsimp [prefixCopiesCirc]
    rw [oracleCircuit_queryCount_append, ih (Nat.le_of_succ_le hk),
      embedOracleCircuit_queryCount, Nat.succ_mul]

lemma prefixCopiesCirc_gateCount {r : ℕ} {a : Fin r → ℕ} {M_copy totalW R : ℕ}
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    (c_copy : OracleCircuit gates12 a M_copy)
    (k : ℕ) (hk : k ≤ R) :
    (prefixCopiesCirc copyEmb c_copy k hk).gateCount = k * c_copy.gateCount := by
  induction k with
  | zero => simp [prefixCopiesCirc, OracleCircuit.gateCount]
  | succ k ih =>
    dsimp [prefixCopiesCirc]
    rw [oracleCircuit_gateCount_append, ih (Nat.le_of_succ_le hk),
      embedOracleCircuit_gateCount, Nat.succ_mul]

lemma prefixCopiesCirc_act {r : ℕ} {a : Fin r → ℕ} {M_copy totalW R : ℕ}
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    (hdisj : ∀ j₁ j₂ : Fin R, j₁ ≠ j₂ → Disjoint (Set.range (copyEmb j₁)) (Set.range (copyEmb j₂)))
    {c_copy : OracleCircuit gates12 a M_copy} (hc : Uncontrolled c_copy)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (k : ℕ) (hk : k ≤ R) :
    let φ := act (c_copy.unitary orc) (zeroKet M_copy)
    ∀ y : Qubits totalW,
      act ((prefixCopiesCirc copyEmb c_copy k hk).unitary orc) (zeroKet totalW) y =
        (∏ j : Fin k, φ (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)) *
          (if ∀ w : Fin totalW,
              (∀ j : Fin k, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)) →
              y w = false then 1 else 0) := by
  intro φ
  induction k with
  | zero =>
    intro y
    simp only [prefixCopiesCirc, OracleCircuit.unitary, List.map_nil, List.reverse_nil,
      List.prod_nil, act_one_vec, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      IsEmpty.forall_iff, forall_true_left]
    simp only [zeroKet, ket, PiLp.single_apply]
    by_cases hy : y = fun _ => false
    · subst hy; simp
    · have hnot : ¬ ∀ w : Fin totalW, y w = false := fun h => hy (funext h)
      rw [if_neg hy, if_neg hnot]
  | succ k ih =>
    intro y
    have hk0 : k ≤ R := Nat.le_of_succ_le hk
    let emb_k := copyEmb ⟨k, hk⟩
    have hunit : (prefixCopiesCirc copyEmb c_copy (k + 1) hk).unitary orc =
        embedOp (c_copy.unitary orc) emb_k *
          (prefixCopiesCirc copyEmb c_copy k hk0).unitary orc := by
      dsimp only [prefixCopiesCirc]
      rw [oracleCircuit_unitary_append, embedOracleCircuit_unitary_of_uncontrolled emb_k hc]
    rw [hunit, act_mul, act_embedOp_apply]
    have hdisj_k : ∀ j : Fin k, Disjoint (Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩))
        (Set.range emb_k) := fun j =>
      hdisj _ _ (by intro heq; have := congrArg Fin.val heq; exact absurd this (Nat.ne_of_lt j.isLt))
    have hsum_single : (∑ u : Qubits M_copy,
          c_copy.unitary orc (y ∘ emb_k) u *
            act ((prefixCopiesCirc copyEmb c_copy k hk0).unitary orc) (zeroKet totalW) (updateOn emb_k y u)) =
        c_copy.unitary orc (y ∘ emb_k) (fun _ => false) *
          act ((prefixCopiesCirc copyEmb c_copy k hk0).unitary orc) (zeroKet totalW)
            (updateOn emb_k y fun _ => false) := by
      rw [Finset.sum_eq_single (fun _ => false)]
      · intro u _ hu
        rw [ih hk0]
        have hnot_clean : ¬ ∀ w : Fin totalW,
            (∀ j : Fin k, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩)) →
            updateOn emb_k y u w = false := by
          intro hclean
          apply hu
          funext i
          have hnot_in : ∀ j : Fin k,
              emb_k i ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩) := fun j hmem =>
            (Set.disjoint_left.mp (hdisj_k j) hmem) ⟨i, rfl⟩
          simpa [updateOn_apply] using hclean (emb_k i) hnot_in
        rw [if_neg hnot_clean, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [ih hk0 (updateOn emb_k y fun _ => false)] at hsum_single
    rw [hsum_single]
    have hφ_emb : c_copy.unitary orc (y ∘ emb_k) (fun _ => false) = φ (y ∘ emb_k) := by
      dsimp only [φ, act, zeroKet, ket]
      simp only [Matrix.mulVec, dotProduct, PiLp.single_apply]
      rw [Finset.sum_eq_single (fun _ => false)]
      · simp
      · intro u _ hu; simp [hu]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hprod_eq : (∏ j : Fin k,
          φ (updateOn emb_k y (fun _ => false) ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩)) =
        ∏ j : Fin k, φ (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩) := by
      refine Finset.prod_congr rfl fun j _ => congrArg (fun z : Qubits M_copy => φ z) ?_
      funext i
      have hnot : copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩ i ∉ Set.range emb_k := fun hmem =>
        (Set.disjoint_left.mp (hdisj_k j) ⟨i, rfl⟩) hmem
      exact updateOn_off emb_k y _ hnot
    have hclean_iff :
        (∀ w : Fin totalW,
            (∀ j : Fin k, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩)) →
            updateOn emb_k y (fun _ => false) w = false) ↔
          (∀ w : Fin totalW,
            (∀ j : Fin (k + 1), w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)) →
            y w = false) := by
      constructor
      · intro h w hw
        have hnot_k : w ∉ Set.range emb_k := hw ⟨k, Nat.lt_succ_self k⟩
        have hnot_prev : ∀ j : Fin k, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩) :=
          fun j => hw j.castSucc
        simpa [updateOn_off emb_k y _ hnot_k] using h w hnot_prev
      · intro h w hw
        by_cases hmem : w ∈ Set.range emb_k
        · obtain ⟨i, rfl⟩ := hmem
          rw [updateOn_apply]
        · rw [updateOn_off emb_k y _ hmem]
          apply h w
          intro j
          refine Fin.lastCases ?_ ?_ j
          · exact hmem
          · intro j'; exact hw j'
    have hcond_eq :
        (if ∀ w : Fin totalW,
            (∀ j : Fin k, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩)) →
            updateOn emb_k y (fun _ => false) w = false then (1 : ℂ) else 0) =
          if ∀ w : Fin totalW,
            (∀ j : Fin (k + 1), w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)) →
            y w = false then 1 else 0 :=
      if_congr hclean_iff rfl rfl
    rw [hφ_emb, hprod_eq, hcond_eq]
    have hprod_succ : (∏ j : Fin (k + 1), φ (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk⟩)) =
        (∏ j : Fin k, φ (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt hk0⟩)) * φ (y ∘ emb_k) := by
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hprod_succ]
    ring

def appendEquiv (m e : ℕ) : Qubits m × Qubits e ≃ Qubits (m + e) where
  toFun p := Fin.append p.1 p.2
  invFun z := (fun i => z (Fin.castAdd e i), fun j => z (Fin.natAdd m j))
  left_inv p := by ext <;> simp
  right_inv z := by funext w; refine Fin.addCases (fun i => by simp) (fun j => by simp) w

def copyProdEquiv {totalW R M_copy anc_sw : ℕ}
    (wireEquiv : Fin totalW ≃ (Fin R × Fin M_copy) ⊕ Fin anc_sw)
    (copyEmb : Fin R → (Fin M_copy ↪ Fin totalW))
    (swapAncEmb : Fin anc_sw ↪ Fin totalW)
    (hcopy : ∀ j i, wireEquiv (copyEmb j i) = Sum.inl (j, i))
    (hanc : ∀ l, wireEquiv (swapAncEmb l) = Sum.inr l) :
    Qubits totalW ≃ (Fin R → Qubits M_copy) × Qubits anc_sw where
  toFun y := (fun j i => y (copyEmb j i), fun l => y (swapAncEmb l))
  invFun p w :=
    match wireEquiv w with
    | Sum.inl (j, i) => p.1 j i
    | Sum.inr l => p.2 l
  left_inv y := by
    funext w
    dsimp only
    rcases h : wireEquiv w with ⟨j, i⟩ | l
    · have hw : w = copyEmb j i := wireEquiv.injective (by rw [h, hcopy])
      rw [hw]
    · have hw : w = swapAncEmb l := wireEquiv.injective (by rw [h, hanc])
      rw [hw]
  right_inv p := by
    ext j i
    · dsimp only; rw [hcopy]
    · dsimp only; rw [hanc]

noncomputable def firstHitMin {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) : Fin R :=
  Finset.min' (Finset.univ.filter fun j : Fin R => f j = true)
    (by rcases hf with ⟨j, hj⟩; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

lemma firstHitMin_spec {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) :
    f (firstHitMin f hf) = true := by
  dsimp only [firstHitMin]
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (Finset.univ.filter fun j : Fin R => f j = true)
      (by rcases hf with ⟨j, hj⟩; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩))).2

lemma firstHitMin_min {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true)
    {j : Fin R} (hj : f j = true) :
    firstHitMin f hf ≤ j := by
  dsimp only [firstHitMin]
  exact Finset.min'_le (Finset.univ.filter fun j : Fin R => f j = true) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

lemma eq_firstHitMin_of_min {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true)
    {j : Fin R} (hj : f j = true) (hmin : ∀ k : Fin R, f k = true → j ≤ k) :
    j = firstHitMin f hf :=
  le_antisymm (hmin _ (firstHitMin_spec f hf)) (firstHitMin_min f hf hj)

/-- Probability amplification and rank-1 post-swap factorization on `m_reg + e` wires. -/
theorem parallel_grover_swap {m_reg e R M_copy anc_sw : ℕ}
    (wireEquiv : Fin (m_reg + e) ≃ (Fin R × Fin M_copy) ⊕ Fin anc_sw)
    (copyEmb : Fin R → (Fin M_copy ↪ Fin (m_reg + e)))
    (swapAncEmb : Fin anc_sw ↪ Fin (m_reg + e))
    (hcopy : ∀ j i, wireEquiv (copyEmb j i) = Sum.inl (j, i))
    (hanc : ∀ l, wireEquiv (swapAncEmb l) = Sum.inr l)
    (degEmb : Fin m_reg ↪ Fin M_copy)
    (flagIdx : Fin M_copy)
    (flag : Fin R ↪ Fin e)
    (hflag : ∀ j : Fin R, Fin.natAdd m_reg (flag j) = copyEmb j flagIdx)
    (φ_copy : EuclideanSpace ℂ (Qubits M_copy))
    (hφ_norm : ‖φ_copy‖ = 1)
    (Ft : EuclideanSpace ℂ (Qubits m_reg))
    (hFt_norm : ‖Ft‖ = 1)
    (β_copy : Qubits M_copy → ℂ)
    (hφ_fac : ∀ w : Qubits M_copy, w flagIdx = true → φ_copy w = Ft (w ∘ degEmb) * β_copy w)
    (hβ_indep : ∀ (w : Qubits M_copy) (x : Qubits m_reg), β_copy (updateOn degEmb w x) = β_copy w)
    (ψ_pre : EuclideanSpace ℂ (Qubits (m_reg + e)))
    (hψ_pre_norm : ‖ψ_pre‖ = 1)
    (hψ_pre_eq : ∀ y : Qubits (m_reg + e),
      ψ_pre y = (∏ j : Fin R, φ_copy (y ∘ copyEmb j)) *
        (if ∀ l : Fin anc_sw, y (swapAncEmb l) = false then 1 else 0))
    (U_swap : Matrix (Qubits (m_reg + e)) (Qubits (m_reg + e)) ℂ)
    (σ τ : Qubits (m_reg + e) → Qubits (m_reg + e))
    (hU_act : ∀ y : Qubits (m_reg + e), (∀ l, y (swapAncEmb l) = false) →
      act U_swap (ket y) = ket (σ y))
    (hστ : ∀ y : Qubits (m_reg + e), (∀ l, y (swapAncEmb l) = false) →
      (∀ l, σ y (swapAncEmb l) = false) ∧ τ (σ y) = y)
    (hτσ : ∀ z : Qubits (m_reg + e), (∀ l, z (swapAncEmb l) = false) →
      (∀ l, τ z (swapAncEmb l) = false) ∧ σ (τ z) = z)
    (hσ_flag : ∀ y : Qubits (m_reg + e), (∀ l, y (swapAncEmb l) = false) →
      ∀ j : Fin R, σ y (Fin.natAdd m_reg (flag j)) = y (Fin.natAdd m_reg (flag j)))
    (hτ_swap_good : ∀ (x : Qubits m_reg) (s : Qubits e)
      (hs : ∃ j : Fin R, s (flag j) = true),
      (∀ l, Fin.append x s (swapAncEmb l) = false) →
      let j0 := firstHitMin (s ∘ flag) hs
      (τ (Fin.append x s) ∘ copyEmb j0 =
        updateOn degEmb (τ (Fin.append (fun _ => false) s) ∘ copyEmb j0) x) ∧
      (∀ j : Fin R, j ≠ j0 →
        τ (Fin.append x s) ∘ copyEmb j = τ (Fin.append (fun _ => false) s) ∘ copyEmb j))
    (hclean_indep : ∀ (x₁ x₂ : Qubits m_reg) (s : Qubits e),
      (∀ l, Fin.append x₁ s (swapAncEmb l) = false) ↔
        (∀ l, Fin.append x₂ s (swapAncEmb l) = false))
    (q1_lo : ℝ)
    (_hq1_pos : 0 ≤ q1_lo)
    (hq1_le : q1_lo ≤ probEvent φ_copy (fun u : Qubits M_copy => u flagIdx = true))
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (hR_bound : (1 - q1_lo) ^ R ≤ ξ ^ 2 / 16) :
    let good : Set (Qubits R) := {f | ∃ j : Fin R, f j = true}
    let ψ := act U_swap ψ_pre
    let P := probEvent ψ (fun z => (fun j : Fin e => z (Fin.natAdd m_reg j)) ∘ flag ∈ good)
    1 - ξ ^ 2 / 16 ≤ P ∧
    ∃ χ : EuclideanSpace ℂ (Qubits e),
      ‖χ‖ = 1 ∧
      ∀ (x : Qubits m_reg) (s : Qubits e), s ∘ flag ∈ good →
        ψ (Fin.append x s) = (Real.sqrt P : ℂ) * Ft x * χ s := by
  classical
  intro good ψ P
  let IsClean : Qubits (m_reg + e) → Prop := fun y => ∀ l : Fin anc_sw, y (swapAncEmb l) = false
  have hψ_pre_clean : ∀ y : Qubits (m_reg + e), ¬ IsClean y → ψ_pre y = 0 := fun y hy => by
    rw [hψ_pre_eq]
    change _ * (if IsClean y then (1 : ℂ) else 0) = 0
    rw [if_neg hy, mul_zero]
  have hψ_eq : ∀ z : Qubits (m_reg + e), ψ z = if IsClean z then ψ_pre (τ z) else 0 := by
    intro z
    dsimp only [ψ]
    have hdecomp : ψ_pre = ∑ y ∈ Finset.univ.filter IsClean, ψ_pre y • ket y := by
      conv_lhs => rw [vec_eq_sum_ket ψ_pre]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro y _ hy
      rw [Finset.mem_filter] at hy
      have hy' : ¬ IsClean y := fun h => hy ⟨Finset.mem_univ _, h⟩
      rw [hψ_pre_clean y hy', zero_smul]
    conv_lhs => rw [hdecomp, act_sum]
    have hact_y : ∀ y ∈ Finset.univ.filter IsClean,
        act U_swap (ψ_pre y • ket y) = ψ_pre y • ket (σ y) := fun y hy => by
      rw [act_smul, hU_act y (Finset.mem_filter.mp hy).2]
    have hvec : (∑ y ∈ Finset.univ.filter IsClean, act U_swap (ψ_pre y • ket y)) =
        ∑ y ∈ Finset.univ.filter IsClean, ψ_pre y • ket (σ y) :=
      Finset.sum_congr rfl hact_y
    rw [hvec]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ket, PiLp.single_apply]
    by_cases hz : IsClean z
    · rw [if_pos hz, Finset.sum_filter, Finset.sum_eq_single (τ z)]
      · rw [if_pos (hτσ z hz).1]
        by_cases heq : z = σ (τ z)
        · rw [if_pos heq, mul_one]
        · exact absurd (hτσ z hz).2.symm heq
      · intro y _ hne
        by_cases hyc : IsClean y
        · have hne_σ : z ≠ σ y := fun h => hne (by rw [h, (hστ y hyc).2])
          rw [if_pos hyc]
          by_cases heq : z = σ y
          · exact absurd heq hne_σ
          · simp [heq]
        · rw [if_neg hyc]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · rw [if_neg hz]
      refine Finset.sum_eq_zero fun y hy => ?_
      have hyc : IsClean y := (Finset.mem_filter.mp hy).2
      have hne_σ : z ≠ σ y := fun h => hz (by rw [h]; exact (hστ y hyc).1)
      by_cases heq : z = σ y
      · exact absurd heq hne_σ
      · simp [heq]
  let goodGlobal : Qubits (m_reg + e) → Prop :=
    fun z => (fun j : Fin R => z (Fin.natAdd m_reg (flag j))) ∈ good
  have hP_def : P = probEvent ψ goodGlobal := rfl
  have hclean_flag : ∀ y : Qubits (m_reg + e), IsClean y → (goodGlobal (σ y) ↔ goodGlobal y) :=
    fun y hy => by
      dsimp only [goodGlobal]
      have heq : (fun j : Fin R => σ y (Fin.natAdd m_reg (flag j))) =
          (fun j : Fin R => y (Fin.natAdd m_reg (flag j))) := funext (hσ_flag y hy)
      rw [heq]
  have hP_eq : P = probEvent ψ_pre goodGlobal := by
    rw [hP_def, probEvent_eq_sum, probEvent_eq_sum]
    have hsub_ψ : (∑ z ∈ Finset.univ.filter goodGlobal, ‖ψ z‖ ^ 2) =
        ∑ z ∈ Finset.univ.filter (fun z => goodGlobal z ∧ IsClean z), ‖ψ z‖ ^ 2 := by
      have hsub : Finset.univ.filter (fun z => goodGlobal z ∧ IsClean z) ⊆ Finset.univ.filter goodGlobal :=
        fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.1⟩
      rw [← Finset.sum_subset hsub]
      intro z hz hnot
      rw [Finset.mem_filter] at hz hnot
      have hnc : ¬ IsClean z := fun hc => hnot ⟨Finset.mem_univ _, hz.2, hc⟩
      rw [hψ_eq z, if_neg hnc, norm_zero, zero_pow (by norm_num)]
    have hsub_pre : (∑ y ∈ Finset.univ.filter goodGlobal, ‖ψ_pre y‖ ^ 2) =
        ∑ y ∈ Finset.univ.filter (fun y => goodGlobal y ∧ IsClean y), ‖ψ_pre y‖ ^ 2 := by
      have hsub : Finset.univ.filter (fun y => goodGlobal y ∧ IsClean y) ⊆ Finset.univ.filter goodGlobal :=
        fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.1⟩
      rw [← Finset.sum_subset hsub]
      intro y hy hnot
      rw [Finset.mem_filter] at hy hnot
      have hnc : ¬ IsClean y := fun hc => hnot ⟨Finset.mem_univ _, hy.2, hc⟩
      rw [hψ_pre_clean y hnc, norm_zero, zero_pow (by norm_num)]
    rw [hsub_ψ, hsub_pre]
    refine Finset.sum_bij (fun z _ => τ z) ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      have hcz := hz.2.2
      refine ⟨Finset.mem_univ _, ?_, (hτσ z hcz).1⟩
      have heq : goodGlobal (σ (τ z)) ↔ goodGlobal (τ z) := hclean_flag (τ z) (hτσ z hcz).1
      rw [(hτσ z hcz).2] at heq
      exact heq.mp hz.2.1
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [Finset.mem_filter] at hz₁ hz₂
      have h1 := (hτσ z₁ hz₁.2.2).2
      have h2 := (hτσ z₂ hz₂.2.2).2
      rw [← h1, heq, h2]
    · intro y hy
      rw [Finset.mem_filter] at hy
      have hyc := hy.2.2
      refine ⟨σ y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hclean_flag y hyc).mpr hy.2.1,
        (hστ y hyc).1⟩, (hστ y hyc).2⟩
    · intro z hz
      rw [Finset.mem_filter] at hz
      rw [hψ_eq z, if_pos hz.2.2]
  let q1 : ℝ := probEvent φ_copy (fun u : Qubits M_copy => u flagIdx = true)
  have hq1_le1 : q1 ≤ 1 := by
    have hsum : q1 + probEvent φ_copy (fun u : Qubits M_copy => ¬ (u flagIdx = true)) = 1 := by
      dsimp only [q1]
      rw [probEvent_eq_sum, probEvent_eq_sum, Finset.sum_filter_add_sum_filter_not,
        ← norm_sq_eq_sum, hφ_norm, one_pow]
    have hnn : 0 ≤ probEvent φ_copy (fun u : Qubits M_copy => ¬ (u flagIdx = true)) :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hP_formula : P = 1 - (1 - q1) ^ R := by
    rw [hP_eq]
    have hsum1 : probEvent ψ_pre goodGlobal + probEvent ψ_pre (fun y => ¬ goodGlobal y) = 1 := by
      rw [probEvent_eq_sum, probEvent_eq_sum, Finset.sum_filter_add_sum_filter_not,
        ← norm_sq_eq_sum, hψ_pre_norm, one_pow]
    have hnot_good : ∀ y : Qubits (m_reg + e),
        (¬ goodGlobal y) ↔ ∀ j : Fin R, (y ∘ copyEmb j) flagIdx = false := fun y => by
      dsimp only [goodGlobal, good]
      simp only [Set.mem_ofPred_eq, not_exists, Bool.not_eq_true, Function.comp_apply, ← hflag]
    have hcomp : probEvent ψ_pre (fun y => ¬ goodGlobal y) = (1 - q1) ^ R := by
      rw [probEvent_eq_sum, Finset.sum_filter]
      let eqv := copyProdEquiv wireEquiv copyEmb swapAncEmb hcopy hanc
      have hsum_eqv :
          (∑ y : Qubits (m_reg + e), if ¬ goodGlobal y then ‖ψ_pre y‖ ^ 2 else 0) =
            ∑ p : (Fin R → Qubits M_copy) × Qubits anc_sw,
              if ∀ j : Fin R, p.1 j flagIdx = false then
                (∏ j : Fin R, ‖φ_copy (p.1 j)‖ ^ 2) *
                  (if p.2 = fun _ => false then 1 else 0)
              else 0 := by
        rw [← Equiv.sum_comp eqv.symm]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hcomp_copy : ∀ j : Fin R, (eqv.symm p) ∘ copyEmb j = p.1 j := fun j => by
          funext i; exact congrFun (congrArg Prod.fst (eqv.right_inv p)) j |> fun hj => congrFun hj i
        have hcomp_anc : (fun l : Fin anc_sw => eqv.symm p (swapAncEmb l)) = p.2 :=
          congrArg Prod.snd (eqv.right_inv p)
        have hclean_p : IsClean (eqv.symm p) ↔ p.2 = fun _ => false := by
          dsimp only [IsClean]
          constructor
          · intro h; funext l; have := congrFun hcomp_anc l; simpa [h l] using this.symm
          · intro h l; have := congrFun hcomp_anc l; simpa [h] using this
        have hng : ¬ goodGlobal (eqv.symm p) ↔ ∀ j : Fin R, p.1 j flagIdx = false := by
          rw [hnot_good]; simp_rw [hcomp_copy]
        rw [hψ_pre_eq]
        change (if ¬ goodGlobal (eqv.symm p) then
            ‖(∏ j : Fin R, φ_copy ((eqv.symm p) ∘ copyEmb j)) *
              (if IsClean (eqv.symm p) then (1 : ℂ) else 0)‖ ^ 2 else 0) = _
        simp_rw [hcomp_copy]
        by_cases hgood_p : ∀ j : Fin R, p.1 j flagIdx = false
        · rw [if_pos (hng.mpr hgood_p), if_pos hgood_p]
          by_cases hc_p : p.2 = fun _ => false
          · rw [if_pos (hclean_p.mpr hc_p), if_pos hc_p, mul_one, mul_one,
              norm_prod, Finset.prod_pow]
          · rw [if_neg (fun h => hc_p (hclean_p.mp h)), if_neg hc_p, mul_zero, norm_zero,
              zero_pow (by norm_num), mul_zero]
        · rw [if_neg (fun h => hgood_p (hng.mp h)), if_neg hgood_p]
      rw [hsum_eqv, Fintype.sum_prod_type]
      have hsum_anc : ∀ f : Fin R → Qubits M_copy,
          (∑ g : Qubits anc_sw,
            if ∀ j : Fin R, f j flagIdx = false then
              (∏ j : Fin R, ‖φ_copy (f j)‖ ^ 2) * (if g = fun _ => false then 1 else 0)
            else 0) =
          if ∀ j : Fin R, f j flagIdx = false then ∏ j : Fin R, ‖φ_copy (f j)‖ ^ 2 else 0 := by
        intro f
        by_cases hf : ∀ j : Fin R, f j flagIdx = false
        · simp_rw [if_pos hf]
          rw [Finset.sum_eq_single (fun _ => false)]
          · simp
          · intro g _ hg; simp [hg]
          · intro h; exact absurd (Finset.mem_univ _) h
        · simp [hf]
      simp_rw [hsum_anc]
      let B := {u : Qubits M_copy // u flagIdx = false}
      have hsum_sub :
          (∑ f : Fin R → Qubits M_copy,
            if ∀ j : Fin R, f j flagIdx = false then ∏ j : Fin R, ‖φ_copy (f j)‖ ^ 2 else 0) =
          ∑ f : Fin R → B, ∏ j : Fin R, ‖φ_copy (f j).1‖ ^ 2 := by
        rw [← Finset.sum_filter]
        let S_f := Finset.univ.filter fun f : Fin R → Qubits M_copy => ∀ j, f j flagIdx = false
        have hcoe : (∑ f ∈ S_f, ∏ j : Fin R, ‖φ_copy (f j)‖ ^ 2) =
            ∑ f : S_f, ∏ j : Fin R, ‖φ_copy (f.1 j)‖ ^ 2 :=
          (Finset.sum_coe_sort S_f (fun f => ∏ j : Fin R, ‖φ_copy (f j)‖ ^ 2)).symm
        let eqvF : S_f ≃ (Fin R → B) :=
          { toFun := fun f j => ⟨f.1 j, (Finset.mem_filter.mp f.2).2 j⟩
            invFun := fun g => ⟨fun j => (g j).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => (g j).2⟩⟩
            left_inv := fun f => rfl
            right_inv := fun g => rfl }
        rw [hcoe]
        exact Fintype.sum_equiv eqvF _ _ fun f => rfl
      rw [hsum_sub, ← Fintype.prod_sum (fun (_ : Fin R) (u : B) => ‖φ_copy u.1‖ ^ 2)]
      have hB_sum : (∑ u : B, ‖φ_copy u.1‖ ^ 2) = 1 - q1 := by
        have hsub_u : (∑ u : B, ‖φ_copy u.1‖ ^ 2) =
            probEvent φ_copy (fun u : Qubits M_copy => ¬ (u flagIdx = true)) := by
          rw [probEvent_eq_sum]
          let S_u := Finset.univ.filter fun u : Qubits M_copy => ¬ (u flagIdx = true)
          have hcoe : (∑ u ∈ S_u, ‖φ_copy u‖ ^ 2) = ∑ u : S_u, ‖φ_copy u.1‖ ^ 2 :=
            (Finset.sum_coe_sort S_u (fun u => ‖φ_copy u‖ ^ 2)).symm
          let eqvU : B ≃ S_u :=
            { toFun := fun u => ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [u.2]⟩⟩
              invFun := fun u => ⟨u.1, Bool.eq_false_iff.mpr (Finset.mem_filter.mp u.2).2⟩
              left_inv := fun u => rfl
              right_inv := fun u => rfl }
          rw [hcoe]
          exact Fintype.sum_equiv eqvU _ _ fun u => rfl
        have hsum_phi : q1 + probEvent φ_copy (fun u : Qubits M_copy => ¬ (u flagIdx = true)) = 1 := by
          dsimp only [q1]
          rw [probEvent_eq_sum, probEvent_eq_sum, Finset.sum_filter_add_sum_filter_not,
            ← norm_sq_eq_sum, hφ_norm, one_pow]
        linarith
      simp_rw [hB_sum, Finset.prod_const, Finset.card_fin]
    linarith
  have hP_lo : 1 - ξ ^ 2 / 16 ≤ P := by
    rw [hP_formula]
    have hpow : (1 - q1) ^ R ≤ (1 - q1_lo) ^ R :=
      pow_le_pow_left₀ (by linarith) (by linarith) R
    linarith
  have hP_pos : 0 < P := by nlinarith
  let G : Qubits e → ℂ := fun s =>
    if hs : s ∘ flag ∈ good then
      let j0 := firstHitMin (s ∘ flag) hs
      let y0 := τ (Fin.append (fun _ : Fin m_reg => false) s)
      (if IsClean (Fin.append (fun _ : Fin m_reg => false) s) then (1 : ℂ) else 0) *
        β_copy (y0 ∘ copyEmb j0) *
        ∏ j ∈ Finset.univ.erase j0, φ_copy (y0 ∘ copyEmb j)
    else 0
  have hψ_fac : ∀ (x : Qubits m_reg) (s : Qubits e), s ∘ flag ∈ good →
      ψ (Fin.append x s) = Ft x * G s := by
    intro x s hs
    have hgood_z : goodGlobal (Fin.append x s) := by
      dsimp only [goodGlobal]
      simpa [Function.comp_def, Fin.append_right] using hs
    rw [hψ_eq]
    by_cases hclean_xs : IsClean (Fin.append x s)
    · have hclean_0s : IsClean (Fin.append (fun _ : Fin m_reg => false) s) :=
        (hclean_indep x (fun _ => false) s).mp hclean_xs
      rw [if_pos hclean_xs, hψ_pre_eq]
      have hclean_τ : IsClean (τ (Fin.append x s)) := (hτσ _ hclean_xs).1
      change (∏ j : Fin R, φ_copy (τ (Fin.append x s) ∘ copyEmb j)) *
          (if IsClean (τ (Fin.append x s)) then (1 : ℂ) else 0) = _
      rw [if_pos hclean_τ, mul_one]
      let j0 := firstHitMin (s ∘ flag) hs
      let y0 := τ (Fin.append (fun _ : Fin m_reg => false) s)
      have hG_eq : G s = β_copy (y0 ∘ copyEmb j0) *
          ∏ j ∈ Finset.univ.erase j0, φ_copy (y0 ∘ copyEmb j) := by
        dsimp only [G]
        rw [dif_pos hs, if_pos hclean_0s, one_mul]
      rw [hG_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)]
      have hτ_swap := hτ_swap_good x s hs hclean_xs
      have hflag_true : (τ (Fin.append x s) ∘ copyEmb j0) flagIdx = true := by
        rw [Function.comp_apply, ← hflag]
        have hστ_id := (hτσ _ hclean_xs).2
        have hsf := hσ_flag _ hclean_τ j0
        rw [hστ_id] at hsf
        rw [← hsf, Fin.append_right]
        exact firstHitMin_spec (s ∘ flag) hs
      have hφ_j0 : φ_copy (τ (Fin.append x s) ∘ copyEmb j0) = Ft x * β_copy (y0 ∘ copyEmb j0) := by
        rw [hφ_fac _ hflag_true]
        have hswap0 : τ (Fin.append x s) ∘ copyEmb j0 = updateOn degEmb (y0 ∘ copyEmb j0) x :=
          hτ_swap.1
        rw [hswap0, updateOn_comp, hβ_indep]
      have hprod_rest :
          (∏ j ∈ Finset.univ.erase j0, φ_copy (τ (Fin.append x s) ∘ copyEmb j)) =
            ∏ j ∈ Finset.univ.erase j0, φ_copy (y0 ∘ copyEmb j) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        have hne : j ≠ j0 := (Finset.mem_erase.mp hj).1
        rw [hτ_swap.2 j hne]
      rw [hφ_j0, hprod_rest]
      ring
    · have hclean_0s : ¬ IsClean (Fin.append (fun _ : Fin m_reg => false) s) := fun h =>
        hclean_xs ((hclean_indep x (fun _ => false) s).mpr h)
      rw [if_neg hclean_xs]
      have hG0 : G s = 0 := by
        dsimp only [G]
        rw [dif_pos hs, if_neg hclean_0s, zero_mul, zero_mul]
      rw [hG0, mul_zero]
  have hP_G : P = ∑ s ∈ Finset.univ.filter (fun s : Qubits e => s ∘ flag ∈ good), ‖G s‖ ^ 2 := by
    rw [hP_def, probEvent_eq_sum, Finset.sum_filter, ← Equiv.sum_comp (appendEquiv m_reg e),
      Fintype.sum_prod_type]
    have hterm : (∑ x : Qubits m_reg, ∑ s : Qubits e,
          if goodGlobal (Fin.append x s) then ‖ψ (Fin.append x s)‖ ^ 2 else 0) =
        ∑ x : Qubits m_reg, ‖Ft x‖ ^ 2 *
          ∑ s ∈ Finset.univ.filter (fun s : Qubits e => s ∘ flag ∈ good), ‖G s‖ ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hgf : goodGlobal (Fin.append x s) ↔ s ∘ flag ∈ good := by
        dsimp only [goodGlobal]
        simp only [Fin.append_right]
        rfl
      by_cases hs : s ∘ flag ∈ good
      · rw [if_pos (hgf.mpr hs), if_pos hs, hψ_fac x s hs, norm_mul, mul_pow]
      · rw [if_neg (fun h => hs (hgf.mp h)), if_neg hs]
    change (∑ x : Qubits m_reg, ∑ s : Qubits e,
        if goodGlobal (Fin.append x s) then ‖ψ (Fin.append x s)‖ ^ 2 else 0) = _
    rw [hterm, ← Finset.sum_mul, ← norm_sq_eq_sum, hFt_norm, one_pow, one_mul]
  let χ : EuclideanSpace ℂ (Qubits e) :=
    WithLp.toLp 2 fun s => if s ∘ flag ∈ good then ((1 / Real.sqrt P : ℝ) : ℂ) * G s else 0
  have hsqrtP_pos : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP_pos
  have hχ_norm : ‖χ‖ = 1 := by
    have hsq : ‖χ‖ ^ 2 = 1 := by
      rw [norm_sq_eq_sum]
      calc (∑ s : Qubits e, ‖χ s‖ ^ 2)
          = ∑ s ∈ Finset.univ.filter (fun s : Qubits e => s ∘ flag ∈ good),
              ((1 / Real.sqrt P : ℝ) ^ 2 * ‖G s‖ ^ 2) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun s _ => ?_
            dsimp only [χ]
            split_ifs with hs
            · rw [norm_mul, Complex.norm_of_nonneg (one_div_nonneg.mpr hsqrtP_pos.le), mul_pow]
            · simp
        _ = (1 / Real.sqrt P) ^ 2 *
              ∑ s ∈ Finset.univ.filter (fun s : Qubits e => s ∘ flag ∈ good), ‖G s‖ ^ 2 :=
            (Finset.mul_sum _ _ _).symm
        _ = (1 / P) * P := by
            rw [← hP_G, div_pow, one_pow, Real.sq_sqrt hP_pos.le]
        _ = 1 := one_div_mul_cancel hP_pos.ne'
    have hnn : 0 ≤ ‖χ‖ := norm_nonneg χ
    nlinarith
  refine ⟨hP_lo, χ, hχ_norm, fun x s hs => ?_⟩
  rw [hψ_fac x s hs]
  dsimp only [χ]
  rw [if_pos hs]
  have hcancel : (Real.sqrt P : ℂ) * ((1 / Real.sqrt P : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_one_div_cancel hsqrtP_pos.ne', Complex.ofReal_one]
  calc Ft x * G s = 1 * Ft x * G s := by ring
    _ = ((Real.sqrt P : ℂ) * ((1 / Real.sqrt P : ℝ) : ℂ)) * Ft x * G s := by rw [hcancel]
    _ = (Real.sqrt P : ℂ) * Ft x * (((1 / Real.sqrt P : ℝ) : ℂ) * G s) := by ring

/-- Base case `n = 0`: return empty circuit `c = []` with `Uncontrolled c`, `0` queries, `0` gates,
and derive contradiction from `‖w‖ = 1` on `EuclideanSpace ℝ (Fin 0)`. -/
lemma theorem_5_3_n_zero {K D q a : ℕ} {ξ C : ℝ} (hC : 0 < C) (hK : 1 ≤ K)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    ∃ (e r : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => 0 * q + 1 + a) (0 * q + e))
      (_flag : Fin r ↪ Fin e) (_good : Set (Qubits r)),
      Uncontrolled c ∧
      (c.queryCount 0 : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) ∧
      (c.gateCount : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
        (0 * (Real.log (2 ^ q) + Real.log (0 * D)) + a) ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), ‖w‖ = 1 → False := by
  refine ⟨1, 1, [], Equiv.refl (Fin 1) |>.toEmbedding, Set.univ, ?_, ?_, ?_, ?_⟩
  · intro s hs; simp at hs
  · have hinv : 2 < 1 / ξ := by rw [lt_div_iff₀ hξ0]; linarith
    have hlog_pos : 0 < Real.log (1 / ξ) := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (Real.log_le_log (by norm_num) hinv.le)
    have hK_nn : 0 ≤ (K : ℝ) ^ (1 / 4 : ℝ) := by positivity
    simp only [OracleCircuit.queryCount, List.countP_nil, Nat.cast_zero]
    positivity
  · have hinv : 2 < 1 / ξ := by rw [lt_div_iff₀ hξ0]; linarith
    have hlog_pos : 0 < Real.log (1 / ξ) := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (Real.log_le_log (by norm_num) hinv.le)
    simp only [OracleCircuit.gateCount, List.countP_nil, Nat.cast_zero, zero_mul, zero_add]
    positivity
  · intro w hw
    have hw0 : w = 0 := Subsingleton.elim w 0
    rw [hw0, norm_zero] at hw
    norm_num at hw

/-! ### 5. Hermite-to-Grover Single-Copy Bridge -/

open QuantumLTF.Membership.Supplement

def snocEquiv (n : ℕ) : Qubits n × Bool ≃ Qubits (n + 1) where
  toFun p := Fin.snoc p.1 p.2
  invFun z := (fun i => z i.castSucc, z (Fin.last n))
  left_inv p := by ext <;> simp
  right_inv z := by funext w; refine Fin.lastCases (by simp) (fun i => by simp) w

lemma good_append_snoc_iff {n q K D a : ℕ} (hD : 2 * K + 1 ≤ D)
    {good : Qubits (n * q + 1 + a) → Bool}
    (hgood_iff : ∀ z : Qubits (n * q + 1 + a),
      good z = true ↔
        z (Fin.castAdd a (Fin.last (n * q))) = true ∧
        (∀ j : Fin a, z (Fin.natAdd (n * q + 1) j) = false) ∧
        (∀ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) < D) ∧
        K ≤ ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ∧
        ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ≤ 2 * K)
    (x : Qubits (n * q)) (y : Bool) (s : Qubits a) :
    good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) = true ↔
      y = true ∧ (∀ j : Fin a, s j = false) ∧
      K ≤ ∑ i : Fin n, bitsToNat (splitReg n q x i) ∧
      ∑ i : Fin n, bitsToNat (splitReg n q x i) ≤ 2 * K := by
  let z := Fin.append (Fin.snoc (α := fun _ => Bool) x y) s
  have hz_y : z (Fin.castAdd a (Fin.last (n * q))) = y := by
    dsimp only [z]; rw [Fin.append_left, Fin.snoc_last]
  have hz_s : ∀ j : Fin a, z (Fin.natAdd (n * q + 1) j) = s j := fun j => by
    dsimp only [z]; rw [Fin.append_right]
  have hz_x : (fun k : Fin (n * q) => z (Fin.castAdd a (Fin.castSucc k))) = x := by
    funext k; dsimp only [z]; rw [Fin.append_left, Fin.snoc_castSucc]
  rw [hgood_iff z, hz_y, hz_x]
  simp_rw [hz_s]
  constructor
  · rintro ⟨hy, hs, _, hk1, hk2⟩; exact ⟨hy, hs, hk1, hk2⟩
  · rintro ⟨hy, hs, hk1, hk2⟩
    refine ⟨hy, hs, fun i => ?_, hk1, hk2⟩
    have hle := Finset.single_le_sum (fun j _ => Nat.zero_le (bitsToNat (splitReg n q x j)))
      (Finset.mem_univ i)
    omega

lemma hermite_singleCopy_bridge {n K D q a anc_g anc_z anc_m : ℕ}
    (_hn : 1 ≤ n) (hK : 1 ≤ K) (hD : 2 * K + 1 ≤ D) (hq : D ≤ 2 ^ q)
    {ξ c_band : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (hc_pos : 0 < c_band)
    (hp_bds : ∀ K' : ℕ, 1 ≤ K' → c_band / Real.sqrt K' ≤ p1D53 K' ∧ p1D53 K' ≤ 1)
    (hbw_eq : ∀ (n' K' : ℕ) (w' : EuclideanSpace ℝ (Fin n')), ‖w'‖ = 1 → bandWeight w' K' = p1D53 K')
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (A : Matrix (Qubits (n * q + 1 + a)) (Qubits (n * q + 1 + a)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits (n * q + 1 + a)) ℂ)
    (F0 Fw : EuclideanSpace ℂ (Qubits (n * q + a)))
    (hA_eq : ∀ (x : Qubits (n * q)) (y : Bool) (s : Qubits a),
      act A (zeroKet (n * q + 1 + a)) (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) =
        (1 / Real.sqrt 2 : ℂ) * (if y then Fw (Fin.append x s) else F0 (Fin.append x s)))
    (hproj : projDist n q a D w Fw ≤ ξ * Real.sqrt (bandWeight w K) / 4)
    (good : Qubits (n * q + 1 + a) → Bool)
    (hgood_iff : ∀ z : Qubits (n * q + 1 + a),
      good z = true ↔
        z (Fin.castAdd a (Fin.last (n * q))) = true ∧
        (∀ j : Fin a, z (Fin.natAdd (n * q + 1) j) = false) ∧
        (∀ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) < D) ∧
        K ≤ ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ∧
        ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ≤ 2 * K)
    (c_good : Circuit gates12 (n * q + 1 + a + anc_g))
    (c_zero : Circuit gates12 (n * q + 1 + a + anc_z))
    (c_mark : Circuit gates12 (n * q + 1 + a + 1 + anc_m))
    (hgood_c : ∀ z : Qubits (n * q + 1 + a),
      act c_good.unitary (ket (padFalse (n * q + 1 + a) anc_g z)) =
        (if good z then (-1 : ℂ) else 1) • ket (padFalse (n * q + 1 + a) anc_g z))
    (hzero_c : ∀ z : Qubits (n * q + 1 + a),
      act c_zero.unitary (ket (padFalse (n * q + 1 + a) anc_z z)) =
        (if z = (fun _ => false) then (-1 : ℂ) else 1) • ket (padFalse (n * q + 1 + a) anc_z z))
    (hmark_c : ∀ (z : Qubits (n * q + 1 + a)) (b : Bool),
      act c_mark.unitary (ket (padFalse (n * q + 1 + a + 1) anc_m (Fin.snoc z b))) =
        ket (padFalse (n * q + 1 + a + 1) anc_m (Fin.snoc z (xor b (good z))))) :
    let s0 := Real.sqrt (p1D53 K / 2)
    let t : ℕ := if s0 ≥ 1 / 5 then 0 else Nat.floor (Real.pi / (4 * s0) - 1)
    let anc_copy := max anc_g (max anc_z anc_m)
    let W := n * q + 1 + a
    let M_copy := W + 1 + anc_copy
    let c_copy := singleCopyGroverCirc c_good c_zero c_mark t
    let φ_copy := act (c_copy.unitary fun _ => A) (zeroKet M_copy)
    let v := bandSlice53 n q a K Fw
    let Ft := ((1 / ‖v‖ : ℝ) : ℂ) • v
    let degEmb : Fin (n * q) ↪ Fin M_copy := ⟨fun i => ⟨i.1, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; exact this)⟩
    let flagIdx : Fin M_copy := ⟨W, by omega⟩
    ∃ β_copy : Qubits M_copy → ℂ,
      ‖φ_copy‖ = 1 ∧
      ‖Ft‖ = 1 ∧
      ‖Ft - bandKet n q K w‖ ≤ ξ ∧
      (3 / 100 : ℝ) ≤ probEvent φ_copy (fun u : Qubits M_copy => u flagIdx = true) ∧
      (2 * (t : ℝ) + 1) ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) ∧
      (∀ u : Qubits M_copy, u flagIdx = true → φ_copy u = Ft (u ∘ degEmb) * β_copy u) ∧
      (∀ (u : Qubits M_copy) (x : Qubits (n * q)), β_copy (updateOn degEmb u x) = β_copy u) := by
  classical
  intro s0 t anc_copy W M_copy c_copy φ_copy v Ft degEmb flagIdx
  have hherm2 := hermite_band_bounds_53.2.1 n K D q a hK hD hq w hw Fw
  have hherm3 := hermite_band_bounds_53.2.2.1 n q a K (le_trans hD hq) Fw
  have hbw_p : bandWeight w K = p1D53 K := hbw_eq n K w hw
  have hp_bdsK := hp_bds K hK
  have hp0 : 0 < p1D53 K := by
    have hK_pos : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr (by exact_mod_cast hK)
    linarith [div_pos hc_pos hK_pos]
  have hp1 : p1D53 K ≤ 1 := hp_bdsK.2
  have happrox_p : ‖v - (Real.sqrt (p1D53 K) : ℂ) • bandKet n q K w‖ ≤ ξ * Real.sqrt (p1D53 K) / 4 := by
    rw [← hbw_p]
    exact le_trans hherm2.2 hproj
  have hwin := amplitude_window_and_error hherm2.1 hp0 hp1 hξ0 hξ1 happrox_p
  rcases hwin with ⟨hv_ne, hlo_s0, hhi_s0, hlt1, hFt_norm, hFt_err⟩
  let φ0 := act A (zeroKet W)
  let φ_good : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then φ0 z else 0
  let φ_bad : EuclideanSpace ℂ (Qubits W) := WithLp.toLp 2 fun z => if good z then 0 else φ0 z
  have hφ_good_apply : ∀ (x : Qubits (n * q)) (y : Bool) (s : Qubits a),
      φ_good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) =
        if y = true ∧ (∀ j : Fin a, s j = false) then (1 / Real.sqrt 2 : ℂ) * v x else 0 := by
    intro x y s
    dsimp only [φ_good]
    have hg_iff := good_append_snoc_iff hD hgood_iff x y s
    by_cases hy : y = true ∧ (∀ j : Fin a, s j = false)
    · have hs0 : s = fun _ : Fin a => false := funext hy.2
      rw [if_pos hy]
      by_cases hdeg : K ≤ ∑ i : Fin n, bitsToNat (splitReg n q x i) ∧
          ∑ i : Fin n, bitsToNat (splitReg n q x i) ≤ 2 * K
      · have hg : good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) = true :=
          hg_iff.mpr ⟨hy.1, hy.2, hdeg.1, hdeg.2⟩
        rw [if_pos hg]
        dsimp only [φ0]
        rw [hA_eq x y s, if_pos hy.1, hs0]
        have hvx := hherm3 x
        dsimp only [v]
        rw [hvx, if_pos hdeg]
      · have hng : ¬ (good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) = true) :=
          fun h => hdeg ((hg_iff.mp h).2.2)
        rw [if_neg hng]
        have hvx := hherm3 x
        dsimp only [v]
        rw [hvx, if_neg hdeg, mul_zero]
    · have hng : ¬ (good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) = true) := by
        intro h
        have hm := hg_iff.mp h
        exact hy ⟨hm.1, hm.2.1⟩
      rw [if_neg hng, if_neg hy]
  have hφ_good_norm : ‖φ_good‖ = (1 / Real.sqrt 2) * ‖v‖ := by
    have hsq : ‖φ_good‖ ^ 2 = ((1 / Real.sqrt 2) * ‖v‖) ^ 2 := by
      rw [norm_sq_eq_sum, ← Equiv.sum_comp (appendEquiv (n * q + 1) a), Fintype.sum_prod_type]
      have hsn : ∀ f : Qubits (n * q + 1) → ℝ,
          (∑ p : Qubits (n * q + 1), f p) = ∑ x : Qubits (n * q), ∑ y : Bool, f (Fin.snoc x y) := by
        intro f
        rw [← Equiv.sum_comp (snocEquiv (n * q)), Fintype.sum_prod_type]
        rfl
      simp_rw [hsn]
      calc (∑ x : Qubits (n * q), ∑ y : Bool, ∑ s : Qubits a,
              ‖φ_good (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s)‖ ^ 2)
          = ∑ x : Qubits (n * q), ((1 / 2 : ℝ) * ‖v x‖ ^ 2) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Fintype.sum_bool]
            have hf0 : (∑ s : Qubits a, ‖φ_good (Fin.append (Fin.snoc (α := fun _ => Bool) x false) s)‖ ^ 2) = 0 := by
              refine Finset.sum_eq_zero fun s _ => ?_
              rw [hφ_good_apply x false s, if_neg (by simp), norm_zero, zero_pow (by norm_num)]
            have ht : (∑ s : Qubits a, ‖φ_good (Fin.append (Fin.snoc (α := fun _ => Bool) x true) s)‖ ^ 2) =
                (1 / 2 : ℝ) * ‖v x‖ ^ 2 := by
              rw [Finset.sum_eq_single (fun _ : Fin a => false)]
              · rw [hφ_good_apply x true (fun _ => false), if_pos ⟨rfl, fun _ => rfl⟩,
                  norm_mul, mul_pow, one_div, norm_inv, Complex.norm_real,
                  Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (by norm_num), one_div]
              · intro s _ hs
                have hne : ¬ (true = true ∧ ∀ j : Fin a, s j = false) := fun h => hs (funext h.2)
                rw [hφ_good_apply x true s, if_neg hne, norm_zero, zero_pow (by norm_num)]
              · intro h; exact absurd (Finset.mem_univ _) h
            rw [ht, hf0, add_zero]
        _ = (1 / 2 : ℝ) * ∑ x : Qubits (n * q), ‖v x‖ ^ 2 := (Finset.mul_sum _ _ _).symm
        _ = ((1 / Real.sqrt 2) * ‖v‖) ^ 2 := by
            rw [← norm_sq_eq_sum, mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    have hnn1 : 0 ≤ ‖φ_good‖ := norm_nonneg _
    have hnn2 : 0 ≤ (1 / Real.sqrt 2) * ‖v‖ := by positivity
    nlinarith
  have hgp : 0 < ‖φ_good‖ := by
    rw [hφ_good_norm]
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    positivity
  have hφ0_norm : ‖φ0‖ = 1 := by
    dsimp only [φ0]
    rw [act_norm_of_mem_unitaryGroup hA]
    simp [zeroKet, ket]
  have hsum_sq : ‖φ_good‖ ^ 2 + ‖φ_bad‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    have hsplit : ∀ z : Qubits W, ‖φ_good z‖ ^ 2 + ‖φ_bad z‖ ^ 2 = ‖φ0 z‖ ^ 2 := fun z => by
      dsimp [φ_good, φ_bad]; split_ifs <;> simp
    rw [← Finset.sum_add_distrib]
    simp_rw [hsplit]
    rw [← norm_sq_eq_sum, hφ0_norm, one_pow]
  have hφ_good_lt1 : ‖φ_good‖ < 1 := by rw [hφ_good_norm]; exact hlt1
  have hbp : 0 < ‖φ_bad‖ := by
    have hsq_pos : 0 < ‖φ_bad‖ ^ 2 := by nlinarith
    exact norm_pos_iff.mpr (fun h => by rw [h, norm_zero, zero_pow (by norm_num)] at hsq_pos; linarith)
  let θ := Real.arcsin ‖φ_good‖
  have hs0_pos : 0 < s0 := Real.sqrt_pos.mpr (by positivity)
  have hs0_le : s0 ≤ 1 / Real.sqrt 2 := by
    have hsq : s0 ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
      dsimp only [s0]
      rw [Real.sq_sqrt (by positivity), div_pow, one_pow, Real.sq_sqrt (by norm_num)]
      linarith
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
    nlinarith
  have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hgp.le
  have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsinθ : Real.sin θ = ‖φ_good‖ := Real.sin_arcsin (by linarith) hφ_good_lt1.le
  have hsin_lo : (7 / 8 : ℝ) * s0 ≤ Real.sin θ := by rw [hsinθ, hφ_good_norm]; exact hlo_s0
  have hsin_hi : Real.sin θ ≤ (9 / 8 : ℝ) * s0 := by rw [hsinθ, hφ_good_norm]; exact hhi_s0
  have hwin_sin := grover_window_bound hs0_pos hs0_le hθ0 hθ1 hsin_lo hsin_hi
  have ht_bound : (2 * (t : ℝ) + 1) ≤ max 1 (Real.pi / 2 * Real.sqrt (2 / c_band)) * (K : ℝ) ^ (1 / 4 : ℝ) :=
    grover_t_bound hK hc_pos hp_bdsK.1 hp_bdsK.2
  have hφ_copy_norm : ‖φ_copy‖ = 1 := by
    dsimp only [φ_copy, c_copy]
    have hU := oracleCircuit_unitary_mem_unitaryGroup_of_uncontrolled
      (singleCopyGroverCirc_uncontrolled c_good c_zero c_mark t)
      (fun _ => A) (fun _ => hA)
    rw [act_norm_of_mem_unitaryGroup hU]
    simp [zeroKet, ket]
  let ψ_good := ((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good
  let ψ_bad := ((1 / ‖φ_bad‖ : ℝ) : ℂ) • φ_bad
  have hψg_norm : ‖ψ_good‖ = 1 := by
    change ‖((1 / ‖φ_good‖ : ℝ) : ℂ) • φ_good‖ = 1
    rw [norm_smul, Complex.norm_of_nonneg (one_div_nonneg.mpr hgp.le), one_div_mul_cancel hgp.ne']
  have hact_grov := singleCopyGroverCirc_act good c_good c_zero c_mark hgood_c hzero_c hmark_c t A hA hgp hbp
  change φ_copy =
      ∑ z : Qubits W,
        ((-1 : ℂ) ^ t * (if good z then (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_good z
                          else (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_bad z)) •
          ket (padFalse (W + 1) anc_copy (Fin.snoc z (good z))) at hact_grov
  let coeff : Qubits W → ℂ := fun z =>
    (-1 : ℂ) ^ t * (if good z then (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_good z
                    else (Real.cos ((2 * (t : ℝ) + 1) * θ) : ℂ) * ψ_bad z)
  let embZ : Qubits W → Qubits M_copy := fun z => padFalse (W + 1) anc_copy (Fin.snoc z (good z))
  have hembZ_inj : Function.Injective embZ := by
    intro z₁ z₂ h
    have h1 := padFalse_inj (W + 1) anc_copy h
    funext i
    have h2 := congrFun h1 i.castSucc
    simpa [Fin.snoc_castSucc] using h2
  have hφ_apply : ∀ u : Qubits M_copy,
      φ_copy u = ∑ z : Qubits W, if u = embZ z then coeff z else 0 := by
    intro u
    rw [hact_grov]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ket, PiLp.single_apply, mul_ite, mul_one, mul_zero]
    refine Finset.sum_congr rfl fun z _ => ?_
    dsimp only [embZ, coeff]
    split_ifs <;> rfl
  have hq1_eq : probEvent φ_copy (fun u : Qubits M_copy => u flagIdx = true) =
      Real.sin ((2 * (t : ℝ) + 1) * θ) ^ 2 := by
    rw [probEvent_eq_sum]
    have hgood_flag : ∀ z : Qubits W, embZ z flagIdx = good z := fun z => by
      have hf : flagIdx = Fin.castAdd anc_copy (Fin.last W) := Fin.ext rfl
      dsimp only [embZ]
      rw [hf, padFalse_castAdd, Fin.snoc_last]
    have hsub : Finset.univ.image (fun z : {z : Qubits W // good z = true} => embZ z.1) ⊆
        Finset.univ.filter (fun u : Qubits M_copy => u flagIdx = true) := by
      intro u hu
      rw [Finset.mem_image] at hu
      rcases hu with ⟨⟨z, hz⟩, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hgood_flag, hz]⟩
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (fun z₁ _ z₂ _ h => Subtype.ext (hembZ_inj h))]
      have hterm : ∀ z : {z : Qubits W // good z = true},
          ‖φ_copy (embZ z.1)‖ ^ 2 = Real.sin ((2 * (t : ℝ) + 1) * θ) ^ 2 * ‖ψ_good z.1‖ ^ 2 := by
        intro ⟨z, hz⟩
        rw [hφ_apply, Finset.sum_eq_single z]
        · rw [if_pos rfl]
          dsimp only [coeff]
          rw [if_pos hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        · intro z' _ hz'; rw [if_neg (fun h => hz' (hembZ_inj h).symm)]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hterm, ← Finset.mul_sum]
      have hψg_sum : (∑ z : {z : Qubits W // good z = true}, ‖ψ_good z.1‖ ^ 2) = 1 := by
        have h1 : (∑ z : Qubits W, ‖ψ_good z‖ ^ 2) = 1 := by rw [← norm_sq_eq_sum, hψg_norm, one_pow]
        have hsub_z : (∑ z : Qubits W, ‖ψ_good z‖ ^ 2) =
            ∑ z ∈ Finset.univ.filter (fun z : Qubits W => good z = true), ‖ψ_good z‖ ^ 2 := by
          rw [← Finset.sum_subset (Finset.subset_univ _)]
          intro z _ hz
          rw [Finset.mem_filter] at hz
          have hng : ¬ (good z = true) := fun h => hz ⟨Finset.mem_univ _, h⟩
          have hz0 : ψ_good z = 0 := by
            dsimp only [ψ_good, φ_good]
            rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
            change _ * (if good z = true then φ0 z else 0) = 0
            rw [if_neg hng, mul_zero]
          rw [hz0, norm_zero, zero_pow (by norm_num)]
        rw [hsub_z] at h1
        let S_z := Finset.univ.filter fun z : Qubits W => good z = true
        have hcoe : (∑ z ∈ S_z, ‖ψ_good z‖ ^ 2) = ∑ z : S_z, ‖ψ_good z.1‖ ^ 2 :=
          (Finset.sum_coe_sort S_z (fun z => ‖ψ_good z‖ ^ 2)).symm
        let eqvZ : {z : Qubits W // good z = true} ≃ S_z :=
          { toFun := fun z => ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩
            invFun := fun z => ⟨z.1, (Finset.mem_filter.mp z.2).2⟩
            left_inv := fun z => rfl
            right_inv := fun z => rfl }
        rw [← h1, hcoe]
        exact Fintype.sum_equiv eqvZ _ _ fun z => rfl
      rw [hψg_sum, mul_one]
    · intro u hu hnot
      have hfu : u flagIdx = true := (Finset.mem_filter.mp hu).2
      have hφ0_u : φ_copy u = 0 := by
        rw [hφ_apply]
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases heq : u = embZ z
        · exfalso
          have hgz : good z = true := by rw [← hgood_flag z, ← heq]; exact hfu
          apply hnot
          rw [Finset.mem_image]
          exact ⟨⟨z, hgz⟩, Finset.mem_univ _, heq.symm⟩
        · rw [if_neg heq]
      rw [hφ0_u, norm_zero, zero_pow (by norm_num)]
  have hq1_lo : (3 / 100 : ℝ) ≤ probEvent φ_copy (fun u : Qubits M_copy => u flagIdx = true) := by
    rw [hq1_eq]; exact hwin_sin
  let isTailGood : Qubits M_copy → Bool := fun u =>
    decide (u ⟨n * q, by omega⟩ = true ∧
      (∀ j : Fin a, u ⟨n * q + 1 + j.1, by omega⟩ = false) ∧
      u flagIdx = true ∧
      (∀ k : Fin anc_copy, u ⟨W + 1 + k.1, by omega⟩ = false))
  let β_copy : Qubits M_copy → ℂ := fun u =>
    if isTailGood u then (-1 : ℂ) ^ t * (Real.sin ((2 * (t : ℝ) + 1) * θ) : ℂ) else 0
  have hβ_indep : ∀ (u : Qubits M_copy) (x : Qubits (n * q)), β_copy (updateOn degEmb u x) = β_copy u := by
    intro u x
    have hy : (⟨n * q, by omega⟩ : Fin M_copy) ∉ Set.range degEmb := by
      rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi; change i.1 = n * q at hv; omega
    have ha : ∀ j : Fin a, (⟨n * q + 1 + j.1, by omega⟩ : Fin M_copy) ∉ Set.range degEmb := by
      intro j ⟨i, hi⟩; have hv := congrArg Fin.val hi; change i.1 = n * q + 1 + j.1 at hv; omega
    have hf : flagIdx ∉ Set.range degEmb := by
      rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi; change i.1 = W at hv; dsimp [W] at hv; omega
    have hanc : ∀ k : Fin anc_copy, (⟨W + 1 + k.1, by omega⟩ : Fin M_copy) ∉ Set.range degEmb := by
      intro k ⟨i, hi⟩; have hv := congrArg Fin.val hi; change i.1 = W + 1 + k.1 at hv; dsimp [W] at hv; omega
    have htail : isTailGood (updateOn degEmb u x) = isTailGood u := by
      dsimp only [isTailGood]
      simp_rw [updateOn_off degEmb u x hy, updateOn_off degEmb u x (ha _),
        updateOn_off degEmb u x hf, updateOn_off degEmb u x (hanc _)]
    dsimp only [β_copy]
    rw [htail]
  refine ⟨β_copy, hφ_copy_norm, hFt_norm, hFt_err, hq1_lo, ht_bound, ?_, hβ_indep⟩
  intro u hu_flag
  by_cases htail : isTailGood u = true
  · have htd := of_decide_eq_true htail
    rcases htd with ⟨hu_y, hu_a, _, hu_anc⟩
    let z0 : Qubits W := Fin.append (Fin.snoc (α := fun _ => Bool) (u ∘ degEmb) true) (fun _ : Fin a => false)
    have hz0_deg : ∀ k : Fin (n * q), z0 (Fin.castAdd a (Fin.castSucc k)) = u (degEmb k) := fun k => by
      dsimp only [z0]; rw [Fin.append_left, Fin.snoc_castSucc]; rfl
    have hz0_y : z0 (Fin.castAdd a (Fin.last (n * q))) = true := by
      dsimp only [z0]; rw [Fin.append_left, Fin.snoc_last]
    have hz0_a : ∀ j : Fin a, z0 (Fin.natAdd (n * q + 1) j) = false := fun j => by
      dsimp only [z0]; rw [Fin.append_right]
    have hu_eq : u = padFalse (W + 1) anc_copy (Fin.snoc z0 true) := by
      funext i
      by_cases hi1 : i.1 < n * q
      · have hidx : i = degEmb ⟨i.1, hi1⟩ := Fin.ext rfl
        have hcast1 : i = Fin.castAdd anc_copy (Fin.castSucc (Fin.castAdd a (Fin.castSucc ⟨i.1, hi1⟩))) :=
          Fin.ext rfl
        calc u i = u (degEmb ⟨i.1, hi1⟩) := congrArg u hidx
          _ = z0 (Fin.castAdd a (Fin.castSucc ⟨i.1, hi1⟩)) := (hz0_deg _).symm
          _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true)
                (Fin.castAdd anc_copy (Fin.castSucc (Fin.castAdd a (Fin.castSucc ⟨i.1, hi1⟩)))) := by
              rw [padFalse_castAdd, Fin.snoc_castSucc]
          _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) i := congrArg _ hcast1.symm
      · by_cases hi2 : i.1 = n * q
        · have hidx : i = ⟨n * q, by omega⟩ := Fin.ext hi2
          have hcast2 : i = Fin.castAdd anc_copy (Fin.castSucc (Fin.castAdd a (Fin.last (n * q)))) :=
            Fin.ext (by simp [hi2])
          calc u i = u ⟨n * q, by omega⟩ := congrArg u hidx
            _ = true := hu_y
            _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true)
                  (Fin.castAdd anc_copy (Fin.castSucc (Fin.castAdd a (Fin.last (n * q))))) := by
                rw [padFalse_castAdd, Fin.snoc_castSucc, hz0_y]
            _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) i := congrArg _ hcast2.symm
        · by_cases hi3 : i.1 < W
          · have hj : i.1 - (n * q + 1) < a := by dsimp [W] at hi3; omega
            have hidx : i = ⟨n * q + 1 + (i.1 - (n * q + 1)), by omega⟩ := Fin.ext (by dsimp; omega)
            have hcast3 : i = Fin.castAdd anc_copy (Fin.castSucc (Fin.natAdd (n * q + 1) ⟨i.1 - (n * q + 1), hj⟩)) :=
              Fin.ext (by simp; omega)
            calc u i = u ⟨n * q + 1 + (i.1 - (n * q + 1)), by omega⟩ := congrArg u hidx
              _ = false := hu_a ⟨i.1 - (n * q + 1), hj⟩
              _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true)
                    (Fin.castAdd anc_copy (Fin.castSucc (Fin.natAdd (n * q + 1) ⟨i.1 - (n * q + 1), hj⟩))) := by
                  rw [padFalse_castAdd, Fin.snoc_castSucc, hz0_a]
              _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) i := congrArg _ hcast3.symm
          · by_cases hi4 : i.1 = W
            · have hidx : i = flagIdx := Fin.ext (by dsimp [flagIdx]; exact hi4)
              have hcast4 : i = Fin.castAdd anc_copy (Fin.last W) := Fin.ext (by simp [hi4])
              calc u i = u flagIdx := congrArg u hidx
                _ = true := hu_flag
                _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) (Fin.castAdd anc_copy (Fin.last W)) := by
                    rw [padFalse_castAdd, Fin.snoc_last]
                _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) i := congrArg _ hcast4.symm
            · have hk : i.1 - (W + 1) < anc_copy := by dsimp [M_copy] at *; omega
              have hidx : i = ⟨W + 1 + (i.1 - (W + 1)), by omega⟩ := Fin.ext (by dsimp; omega)
              have hcast5 : i = Fin.natAdd (W + 1) ⟨i.1 - (W + 1), hk⟩ := Fin.ext (by simp; omega)
              calc u i = u ⟨W + 1 + (i.1 - (W + 1)), by omega⟩ := congrArg u hidx
                _ = false := hu_anc ⟨i.1 - (W + 1), hk⟩
                _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) (Fin.natAdd (W + 1) ⟨i.1 - (W + 1), hk⟩) := by
                    rw [padFalse_natAdd]
                _ = padFalse (W + 1) anc_copy (Fin.snoc z0 true) i := congrArg _ hcast5.symm
    by_cases hgood_z0 : good z0 = true
    · have hu_emb : u = embZ z0 := by dsimp only [embZ]; rw [hgood_z0]; exact hu_eq
      rw [hφ_apply, Finset.sum_eq_single z0]
      · rw [if_pos hu_emb]
        dsimp only [coeff, β_copy]
        rw [if_pos hgood_z0, if_pos htail]
        have hψg_val : ψ_good z0 = Ft (u ∘ degEmb) := by
          have h1 := hφ_good_apply (u ∘ degEmb) true (fun _ => false)
          rw [if_pos ⟨rfl, fun _ => rfl⟩] at h1
          have hz_eq : z0 = Fin.append (Fin.snoc (α := fun _ => Bool) (u ∘ degEmb) true) (fun _ : Fin a => false) := rfl
          rw [← hz_eq] at h1
          have hdiv_r : (1 / ‖φ_good‖ : ℝ) = (1 / ‖v‖ : ℝ) * Real.sqrt 2 := by
            rw [hφ_good_norm]
            have hsqrt2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
            have hv_ne' : ‖v‖ ≠ 0 := (norm_pos_iff.mpr hv_ne).ne'
            field_simp
          change ((1 / ‖φ_good‖ : ℝ) : ℂ) * φ_good z0 = ((1 / ‖v‖ : ℝ) : ℂ) * v (u ∘ degEmb)
          rw [h1, hdiv_r, Complex.ofReal_mul]
          have hcancel : (Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ) = 1 := by
            rw [mul_one_div_cancel (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne')]
          calc ((1 / ‖v‖ : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) * ((1 / Real.sqrt 2 : ℂ) * v (u ∘ degEmb))
              = ((1 / ‖v‖ : ℝ) : ℂ) * ((Real.sqrt 2 : ℂ) * (1 / Real.sqrt 2 : ℂ)) * v (u ∘ degEmb) := by ring
            _ = ((1 / ‖v‖ : ℝ) : ℂ) * 1 * v (u ∘ degEmb) := by rw [hcancel]
            _ = ((1 / ‖v‖ : ℝ) : ℂ) * v (u ∘ degEmb) := by ring
        rw [hψg_val]
        ring
      · intro z' _ hz'; rw [if_neg (fun h => hz' (hembZ_inj (hu_emb.symm.trans h)).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hφ0 : φ_copy u = 0 := by
        rw [hφ_apply]
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases heq : u = embZ z
        · exfalso
          have huf : u flagIdx = good z := by
            rw [heq]; dsimp only [embZ]
            have hf : flagIdx = Fin.castAdd anc_copy (Fin.last W) := Fin.ext rfl
            rw [hf, padFalse_castAdd, Fin.snoc_last]
          have hz_eq_z0 : z = z0 := by
            funext k
            have h1 := congrFun (congrArg (· ∘ Fin.castAdd anc_copy) heq) k.castSucc
            have h2 := congrFun (congrArg (· ∘ Fin.castAdd anc_copy) hu_eq) k.castSucc
            have hl := h1.symm.trans h2
            simpa [embZ, padFalse_castAdd, Fin.snoc_castSucc] using hl
          rw [hz_eq_z0, hu_flag] at huf
          exact hgood_z0 huf.symm
        · rw [if_neg heq]
      have hdeg_false : ¬ (K ≤ ∑ i : Fin n, bitsToNat (splitReg n q (u ∘ degEmb) i) ∧
          ∑ i : Fin n, bitsToNat (splitReg n q (u ∘ degEmb) i) ≤ 2 * K) := by
        intro hdeg
        exact hgood_z0 ((good_append_snoc_iff hD hgood_iff (u ∘ degEmb) true (fun _ => false)).mpr
          ⟨rfl, fun _ => rfl, hdeg.1, hdeg.2⟩)
      have hv0 : v (u ∘ degEmb) = 0 := by
        dsimp only [v]; rw [hherm3 (u ∘ degEmb), if_neg hdeg_false]
      have hFt0 : Ft (u ∘ degEmb) = 0 := by
        change ((1 / ‖v‖ : ℝ) : ℂ) * v (u ∘ degEmb) = 0
        rw [hv0, mul_zero]
      rw [hφ0, hFt0, zero_mul]
  · have hβ0 : β_copy u = 0 := by dsimp only [β_copy]; rw [if_neg htail]
    have hφ0 : φ_copy u = 0 := by
      rw [hφ_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases heq : u = embZ z
      · exfalso
        have hgood_z : good z = true := by
          rw [← hu_flag, heq]; dsimp only [embZ]
          have hf : flagIdx = Fin.castAdd anc_copy (Fin.last W) := Fin.ext rfl
          rw [hf, padFalse_castAdd, Fin.snoc_last]
        have hcompW : ∀ i : Fin W, u ⟨i.1, by omega⟩ = z i := fun i => by
          rw [heq]; dsimp only [embZ]
          have hcast : (⟨i.1, by omega⟩ : Fin M_copy) = Fin.castAdd anc_copy i.castSucc := Fin.ext rfl
          rw [hcast, padFalse_castAdd, Fin.snoc_castSucc]
        have hgz := (hgood_iff z).mp hgood_z
        have hu_y : u ⟨n * q, by omega⟩ = true := by
          have h1 := hcompW (Fin.castAdd a (Fin.last (n * q)))
          have h2 : (⟨n * q, by omega⟩ : Fin M_copy) = ⟨(Fin.castAdd a (Fin.last (n * q))).1, by dsimp [W]; omega⟩ :=
            Fin.ext (by simp)
          rw [h2, h1]; exact hgz.1
        have hu_a : ∀ j : Fin a, u ⟨n * q + 1 + j.1, by omega⟩ = false := fun j => by
          have h1 := hcompW (Fin.natAdd (n * q + 1) j)
          have h2 : (⟨n * q + 1 + j.1, by omega⟩ : Fin M_copy) = ⟨(Fin.natAdd (n * q + 1) j).1, by dsimp [W]; omega⟩ :=
            Fin.ext (by simp)
          rw [h2, h1]; exact hgz.2.1 j
        have hu_anc : ∀ k : Fin anc_copy, u ⟨W + 1 + k.1, by omega⟩ = false := fun k => by
          rw [heq]; dsimp only [embZ]
          have hcast : (⟨W + 1 + k.1, by omega⟩ : Fin M_copy) = Fin.natAdd (W + 1) k := Fin.ext rfl
          rw [hcast, padFalse_natAdd]
        exact htail (decide_eq_true ⟨hu_y, hu_a, hu_flag, hu_anc⟩)
      · rw [if_neg heq]
    rw [hφ0, hβ0, mul_zero]

/-! ### 6. Final `band_circuits_53` Bridge and Top-Level `solution` -/

lemma uncontrolled_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    {c₁ c₂ : OracleCircuit S a m} (h₁ : Uncontrolled c₁) (h₂ : Uncontrolled c₂) :
    Uncontrolled (c₁ ++ c₂) := by
  intro s hs
  rcases List.mem_append.mp hs with hs1 | hs2
  · exact h₁ s hs1
  · exact h₂ s hs2

lemma circuits_firstTrue53_eq {R : ℕ} (f : Qubits R) (hf : ∃ j : Fin R, f j = true) :
    QuantumLTF.Membership.Supplement.firstTrue53 f hf = firstHitMin f hf := by
  have hsp := QuantumLTF.Membership.Supplement.firstTrue53_spec f hf
  refine eq_firstHitMin_of_min f hf hsp.1 fun k hk => ?_
  by_contra hlt
  have hlt' : k < QuantumLTF.Membership.Supplement.firstTrue53 f hf := Nat.lt_of_not_ge hlt
  have hfalse := hsp.2 k hlt'
  rw [hk] at hfalse
  exact absurd hfalse (by decide)

def swapBlockEmb53 (R m_reg a anc_copy anc_sw : ℕ) (hR : 1 ≤ R) :
    Fin ((R * m_reg) + R + anc_sw) ↪ Fin (m_reg + e53 R m_reg a anc_copy anc_sw) where
  toFun i := ⟨i.1, by
    have htot := e53_total_eq (R := R) (m_reg := m_reg) (a := a) (anc_copy := anc_copy) (anc_sw := anc_sw) hR
    omega⟩
  inj' _ _ h := Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; exact hv)

lemma copyEmb53_ge_of_tail (R m_reg a anc_copy anc_sw : ℕ) (hR : 1 ≤ R) (hm : 1 ≤ m_reg)
    (j : Fin R) (k : Fin ((m_reg + 1 + a) + 1 + anc_copy))
    (hk1 : m_reg ≤ k.1) (hk2 : k.1 ≠ m_reg + 1 + a) :
    (R * m_reg) + R + anc_sw ≤ (copyEmb53 (a := a) (anc_copy := anc_copy) (anc_sw := anc_sw) hR hm j k).1 := by
  have hnot1 : ¬ k.1 < m_reg := by omega
  simp only [copyEmb53, Function.Embedding.coeFn_mk, wireEquiv53, Equiv.coe_fn_symm_mk]
  rw [dif_neg hnot1]
  by_cases hltW : k.1 < m_reg + 1 + a
  · rw [dif_pos hltW]; dsimp; omega
  · rw [dif_neg hltW, dif_neg hk2]; dsimp; omega

lemma theorem_5_3_n_pos (B : BandCircuits53) {c_band : ℝ} (hc_band : 0 < c_band)
    (hp_bds : ∀ K : ℕ, 1 ≤ K → c_band / Real.sqrt K ≤ p1D53 K ∧ p1D53 K ≤ 1)
    (hbw_eq : ∀ (n K : ℕ) (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 → bandWeight w K = p1D53 K)
    {n K D q a : ℕ} {ξ : ℝ}
    (hn : 1 ≤ n) (hK : 1 ≤ K) (hD : 2 * K + 1 ≤ D) (hq : D ≤ 2 ^ q)
    (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) :
    let C_circ := max 1 B.C_circ
    let C_q := max 1 (Real.pi / 2 * Real.sqrt (2 / c_band))
    let C_R := 6 / Real.log (100 / 97) + 3 / Real.log 2
    let C_tot := max (C_R * C_q) ((8 * C_circ / Real.log 2) * C_R * C_q)
    ∃ (e r : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1 + a) (n * q + e))
      (flag : Fin r ↪ Fin e) (good : Set (Qubits r)),
      Uncontrolled c ∧
      (c.queryCount 0 : ℝ) ≤ C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) ∧
      (c.gateCount : ℝ) ≤ C_tot * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
        (n * (Real.log (2 ^ q) + Real.log (n * D)) + a) ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
      ∀ A : Matrix (Qubits (n * q + 1 + a)) (Qubits (n * q + 1 + a)) ℂ,
        A ∈ Matrix.unitaryGroup (Qubits (n * q + 1 + a)) ℂ →
      ∀ F0 Fw : EuclideanSpace ℂ (Qubits (n * q + a)),
        (∀ (x : Qubits (n * q)) (y : Bool) (s : Qubits a),
          act A (zeroKet (n * q + 1 + a)) (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) =
            (1 / Real.sqrt 2 : ℂ) * (if y then Fw (Fin.append x s) else F0 (Fin.append x s))) →
        projDist n q a D w Fw ≤ ξ * Real.sqrt (bandWeight w K) / 4 →
        open Classical in
        let ψ := act (c.unitary fun _ => A) (zeroKet (n * q + e))
        let P := probEvent ψ (fun z => (fun j : Fin e => z (Fin.natAdd (n * q) j)) ∘ flag ∈ good)
        1 - ξ ^ 2 / 16 ≤ P ∧
        ∃ (Ft : EuclideanSpace ℂ (Qubits (n * q))) (χ : EuclideanSpace ℂ (Qubits e)),
          ‖Ft‖ = 1 ∧ ‖χ‖ = 1 ∧ ‖Ft - bandKet n q K w‖ ≤ ξ ∧
          ∀ (x : Qubits (n * q)) (s : Qubits e), s ∘ flag ∈ good →
            ψ (Fin.append x s) = (Real.sqrt P : ℂ) * Ft x * χ s := by
  classical
  intro C_circ C_q C_R C_tot
  have hCcirc_pos : 0 < C_circ := lt_of_lt_of_le (by norm_num) (le_max_left 1 B.C_circ)
  have hBC_le : B.C_circ ≤ C_circ := le_max_right 1 B.C_circ
  have hq2 : 2 ≤ q := by
    by_contra hq_lt
    have hq1 : q ≤ 1 := by omega
    have hpow : 2 ^ q ≤ 2 := by
      calc 2 ^ q ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hq1
        _ = 2 := by norm_num
    omega
  let m_reg := n * q
  have hm_reg : 1 ≤ m_reg := Nat.mul_pos hn (by omega)
  let W := m_reg + 1 + a
  let s0 := Real.sqrt (p1D53 K / 2)
  let t : ℕ := if s0 ≥ 1 / 5 then 0 else Nat.floor (Real.pi / (4 * s0) - 1)
  let R : ℕ := Nat.ceil (Real.log (16 / ξ ^ 2) / Real.log (100 / 97)) + 2
  have hR1 : 1 ≤ R := by dsimp [R]; omega
  let c_good := B.goodReflectCircuit n K D q a
  let c_zero := B.zeroReflectCircuit n q a
  let c_mark := B.goodMarkerCircuit n K D q a
  let anc_g := B.ancGoodRefl n K D q a
  let anc_z := B.ancZeroRefl n q a
  let anc_m := B.ancMarker n K D q a
  let anc_copy := max anc_g (max anc_z anc_m)
  let M_copy := W + 1 + anc_copy
  let c_copy := singleCopyGroverCirc c_good c_zero c_mark t
  let anc_sw := B.ancFirstHitSwap R m_reg
  let c_swap := B.firstHitSwapCircuit R m_reg
  let e := e53 R m_reg a anc_copy anc_sw
  let flag : Fin R ↪ Fin e := flag53 R m_reg a anc_copy anc_sw
  let good : Set (Qubits R) := {f | ∃ j : Fin R, f j = true}
  let copyEmb := copyEmb53 (a := a) (anc_copy := anc_copy) (anc_sw := anc_sw) hR1 hm_reg
  let swapAncEmb := swapAncEmb53 (a := a) (anc_copy := anc_copy) (anc_sw := anc_sw) hR1 hm_reg
  let emb_swap := swapBlockEmb53 R m_reg a anc_copy anc_sw hR1
  let c_pre : OracleCircuit gates12 (fun _ : Fin 1 => W) (m_reg + e) :=
    prefixCopiesCirc copyEmb c_copy R le_rfl
  let c : OracleCircuit gates12 (fun _ : Fin 1 => W) (m_reg + e) :=
    c_pre ++ ((embedCircuit emb_swap c_swap).map OracleStep.gate)
  have hc_pre_un : Uncontrolled c_pre :=
    prefixCopiesCirc_uncontrolled copyEmb (singleCopyGroverCirc_uncontrolled c_good c_zero c_mark t) R le_rfl
  have hc_un : Uncontrolled c := uncontrolled_append hc_pre_un (uncontrolled_lift _)
  have hq_t : (2 * (t : ℝ) + 1) ≤ C_q * (K : ℝ) ^ (1 / 4 : ℝ) :=
    grover_t_bound hK hc_band (hp_bds K hK).1 (hp_bds K hK).2
  have hR_b : (R : ℝ) ≤ C_R * Real.log (1 / ξ) := amplification_R_bound hξ0 hξ1
  have hasymp := asymptotic_bounds_n_pos (a := a) hn hK hD hq hξ0 hξ1 hc_band hCcirc_pos t R hq_t hR_b
  refine ⟨e, R, c, flag, good, hc_un, ?_, ?_, ?_⟩
  · have hqc : c.queryCount 0 = R * (2 * t + 1) := by
      dsimp only [c, c_pre, c_copy]
      rw [oracleCircuit_queryCount_append, oracleCircuit_queryCount_lift, add_zero,
        prefixCopiesCirc_queryCount, singleCopyGroverCirc_queryCount]
    rw [hqc]
    exact hasymp.2.1
  · have hgc : c.gateCount = R * (t * (c_good.length + c_zero.length) + c_mark.length) + c_swap.length := by
      dsimp only [c, c_pre, c_copy]
      rw [oracleCircuit_gateCount_append, oracleCircuit_gateCount_lift, embedCircuit_length,
        prefixCopiesCirc_gateCount, singleCopyGroverCirc_gateCount]
    let ℓ : ℕ := Nat.clog 2 (n * D + 2) + 1
    let B_sz : ℝ := C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1)
    have hB_nn : 0 ≤ B_sz := by dsimp [B_sz]; positivity
    have hℓ_ge : (Nat.clog 2 (n * D + 2) + 1 : ℝ) ≤ (ℓ : ℝ) + 1 := by
      dsimp [ℓ]; push_cast; linarith
    have hcgood_le : (c_good.length : ℝ) ≤ B_sz := by
      have h1 := B.goodReflect_size n K D q a
      have h2 : (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1 ≤
          (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1 := by
        have hm := mul_le_mul_of_nonneg_left hℓ_ge (Nat.cast_nonneg n)
        linarith
      have h3 : B.C_circ * ((n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1) ≤ B_sz :=
        mul_le_mul hBC_le h2 (by positivity) hCcirc_pos.le
      exact le_trans h1 h3
    have hcmark_le : (c_mark.length : ℝ) ≤ B_sz := by
      have h1 := B.goodMarker_size n K D q a
      have h2 : (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1 ≤
          (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1 := by
        have hm := mul_le_mul_of_nonneg_left hℓ_ge (Nat.cast_nonneg n)
        linarith
      have h3 : B.C_circ * ((n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1) ≤ B_sz :=
        mul_le_mul hBC_le h2 (by positivity) hCcirc_pos.le
      exact le_trans h1 h3
    have hczero_le : (c_zero.length : ℝ) ≤ B_sz := by
      have h1 := B.zeroReflect_size n q a
      have h2 : (n : ℝ) * (q : ℝ) + (a : ℝ) + 1 ≤ (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1 := by
        have hmul : (n : ℝ) * (q : ℝ) ≤ (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) ℓ]) (Nat.cast_nonneg (α := ℝ) n)
        linarith
      have h3 : B.C_circ * ((n : ℝ) * (q : ℝ) + (a : ℝ) + 1) ≤ B_sz :=
        mul_le_mul hBC_le h2 (by positivity) hCcirc_pos.le
      exact le_trans h1 h3
    have hcswap_le : (c_swap.length : ℝ) ≤ (R : ℝ) * B_sz := by
      have h1 := B.firstHitSwap_size R m_reg
      have h2 : (m_reg : ℝ) + 1 ≤ (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1 := by
        have hm' : (m_reg : ℝ) = (n : ℝ) * (q : ℝ) := by dsimp [m_reg]; push_cast; ring
        have hmul : (n : ℝ) * (q : ℝ) ≤ (n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) ℓ]) (Nat.cast_nonneg (α := ℝ) n)
        linarith [Nat.cast_nonneg (α := ℝ) a]
      have h3 : B.C_circ * (R : ℝ) * ((m_reg : ℝ) + 1) ≤ (R : ℝ) * B_sz := by
        calc B.C_circ * (R : ℝ) * ((m_reg : ℝ) + 1)
            = (R : ℝ) * (B.C_circ * ((m_reg : ℝ) + 1)) := by ring
          _ ≤ (R : ℝ) * (C_circ * ((n : ℝ) * ((q : ℝ) + (ℓ : ℝ) + 1) + (a : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hBC_le h2 (by positivity) hCcirc_pos.le) (Nat.cast_nonneg R)
      exact le_trans (by simpa [m_reg] using h1) h3
    have hgate_le : (c.gateCount : ℝ) ≤ (R : ℝ) * (2 * (t : ℝ) + 2) * B_sz := by
      rw [hgc]; push_cast
      have hcp : (R : ℝ) * ((t : ℝ) * ((c_good.length : ℝ) + (c_zero.length : ℝ)) + (c_mark.length : ℝ)) ≤
          (R : ℝ) * ((t : ℝ) * (B_sz + B_sz) + B_sz) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg R)
        exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add hcgood_le hczero_le) (Nat.cast_nonneg t)) hcmark_le
      linarith
    exact le_trans hgate_le hasymp.2.2
  · intro w hw A hA F0 Fw hA_eq hproj
    let goodPred := isGoodBasis53 n q K D a
    have hgood_iff : ∀ z : Qubits (n * q + 1 + a),
        goodPred z = true ↔
          z (Fin.castAdd a (Fin.last (n * q))) = true ∧
          (∀ j : Fin a, z (Fin.natAdd (n * q + 1) j) = false) ∧
          (∀ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) < D) ∧
          K ≤ ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ∧
          ∑ i : Fin n, bitsToNat (splitReg n q (fun k => z (Fin.castAdd a (Fin.castSucc k))) i) ≤ 2 * K := by
      intro z
      dsimp only [goodPred, isGoodBasis53]
      rw [decide_eq_true_eq]
      rfl
    have hgood_c : ∀ z : Qubits (n * q + 1 + a),
        act c_good.unitary (ket (padFalse (n * q + 1 + a) anc_g z)) =
          (if goodPred z then (-1 : ℂ) else 1) • ket (padFalse (n * q + 1 + a) anc_g z) :=
      B.goodReflect_act n K D q a
    have hzero_c : ∀ z : Qubits (n * q + 1 + a),
        act c_zero.unitary (ket (padFalse (n * q + 1 + a) anc_z z)) =
          (if z = (fun _ => false) then (-1 : ℂ) else 1) • ket (padFalse (n * q + 1 + a) anc_z z) :=
      B.zeroReflect_act n q a
    have hmark_c : ∀ (z : Qubits (n * q + 1 + a)) (b : Bool),
        act c_mark.unitary (ket (padFalse (n * q + 1 + a + 1) anc_m (Fin.snoc z b))) =
          ket (padFalse (n * q + 1 + a + 1) anc_m (Fin.snoc z (xor b (goodPred z)))) :=
      B.goodMarker_act n K D q a
    have hbridge := hermite_singleCopy_bridge hn hK hD hq hξ0 hξ1 hc_band hp_bds hbw_eq
      w hw A hA F0 Fw hA_eq hproj goodPred hgood_iff c_good c_zero c_mark hgood_c hzero_c hmark_c
    rcases hbridge with ⟨β_copy, hφ_norm, hFt_norm, hFt_err, hq1_lo, _ht_b, hφ_fac, hβ_indep⟩
    let φ_copy := act (c_copy.unitary fun _ => A) (zeroKet M_copy)
    let v := bandSlice53 n q a K Fw
    let Ft := ((1 / ‖v‖ : ℝ) : ℂ) • v
    let degEmb : Fin m_reg ↪ Fin M_copy :=
      ⟨fun i => ⟨i.1, by dsimp [M_copy, W]; omega⟩, fun _ _ h => Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; exact hv)⟩
    let flagIdx : Fin M_copy := ⟨W, by dsimp [M_copy]; omega⟩
    let ψ_pre := act (c_pre.unitary fun _ => A) (zeroKet (m_reg + e))
    have hψ_pre_norm : ‖ψ_pre‖ = 1 := by
      dsimp only [ψ_pre]
      have hU := oracleCircuit_unitary_mem_unitaryGroup_of_uncontrolled hc_pre_un (fun _ => A) (fun _ => hA)
      rw [act_norm_of_mem_unitaryGroup hU]
      simp [zeroKet, ket]
    have hdisj : ∀ j₁ j₂ : Fin R, j₁ ≠ j₂ → Disjoint (Set.range (copyEmb j₁)) (Set.range (copyEmb j₂)) := by
      intro j₁ j₂ hne
      rw [Set.disjoint_left]
      rintro _ ⟨i₁, rfl⟩ ⟨i₂, h2⟩
      have h' := congrArg (wireEquiv53 hR1 hm_reg) h2
      change (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inl (j₂, i₂))) =
        (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inl (j₁, i₁))) at h'
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
      exact hne ((Prod.mk.inj (Sum.inl.inj h')).1).symm
    have hclean_equiv : ∀ y : Qubits (m_reg + e),
        (∀ x : Fin (m_reg + e), (∀ j : Fin R, x ∉ Set.range (copyEmb j)) → y x = false) ↔
          ∀ l : Fin anc_sw, y (swapAncEmb l) = false := by
      intro y
      constructor
      · intro h l
        apply h (swapAncEmb l)
        rintro j ⟨i, hi⟩
        have h' := congrArg (wireEquiv53 hR1 hm_reg) hi
        change (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inl (j, i))) =
          (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inr l)) at h'
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
        cases h'
      · intro h x hx
        rcases heqv : wireEquiv53 hR1 hm_reg x with ⟨j, i⟩ | l
        · exfalso
          apply hx j
          exact ⟨i, (wireEquiv53 hR1 hm_reg).injective (by
            change (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inl (j, i))) = _
            rw [Equiv.apply_symm_apply, heqv])⟩
        · have hxl : x = swapAncEmb l := (wireEquiv53 hR1 hm_reg).injective (by
            change _ = (wireEquiv53 hR1 hm_reg) ((wireEquiv53 hR1 hm_reg).symm (Sum.inr l))
            rw [Equiv.apply_symm_apply, heqv])
          rw [hxl]
          exact h l
    have hψ_pre_eq : ∀ y : Qubits (m_reg + e),
        ψ_pre y = (∏ j : Fin R, φ_copy (y ∘ copyEmb j)) *
          (if ∀ l : Fin anc_sw, y (swapAncEmb l) = false then 1 else 0) := by
      intro y
      have hpa := prefixCopiesCirc_act copyEmb hdisj
        (singleCopyGroverCirc_uncontrolled c_good c_zero c_mark t) (fun _ => A) R le_rfl y
      change ψ_pre y = (∏ j : Fin R, φ_copy (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt le_rfl⟩)) *
          (if ∀ w : Fin (m_reg + e), (∀ j : Fin R, w ∉ Set.range (copyEmb ⟨j.1, lt_of_lt_of_le j.isLt le_rfl⟩)) →
            y w = false then 1 else 0) at hpa
      rw [hpa]
      have hprod : (∏ j : Fin R, φ_copy (y ∘ copyEmb ⟨j.1, lt_of_lt_of_le j.isLt le_rfl⟩)) =
          ∏ j : Fin R, φ_copy (y ∘ copyEmb j) := rfl
      rw [hprod]
      congr 1
      exact if_congr (by simpa using hclean_equiv y) rfl rfl
    have hflag_eq : ∀ j : Fin R, Fin.natAdd m_reg (flag j) = copyEmb j flagIdx := fun j =>
      copyEmb53_flag hR1 hm_reg j
    let blocksOf : Qubits (m_reg + e) → Fin R → Qubits m_reg := fun y j i => y (copyEmb j (degEmb i))
    let flagsOf : Qubits (m_reg + e) → Qubits R := fun y j => y (Fin.natAdd m_reg (flag j))
    let blockSwapY : Qubits (m_reg + e) → Qubits ((R * m_reg) + R + anc_sw) := fun y =>
      Fin.append (Fin.append (flatReg R m_reg (swappedBlocks53 (blocksOf y) (flagsOf y))) (flagsOf y))
        (fun _ : Fin anc_sw => false)
    let σ : Qubits (m_reg + e) → Qubits (m_reg + e) := fun y => updateOn emb_swap y (blockSwapY y)
    have hcomp_swap : ∀ y : Qubits (m_reg + e), (∀ l : Fin anc_sw, y (swapAncEmb l) = false) →
        y ∘ emb_swap =
          Fin.append (Fin.append (flatReg R m_reg (blocksOf y)) (flagsOf y)) (fun _ : Fin anc_sw => false) := by
      intro y hclean
      funext u
      refine Fin.addCases (fun u₁ => ?_) (fun l => ?_) u
      · refine Fin.addCases (fun k => ?_) (fun j => ?_) u₁
        · rw [Function.comp_apply, Fin.append_left, Fin.append_left]
          have hpair : k = finProdFinEquiv (finProdFinEquiv.symm k) := (finProdFinEquiv.apply_symm_apply k).symm
          let p := finProdFinEquiv.symm k
          have hidx_eq : emb_swap (Fin.castAdd anc_sw (Fin.castAdd R k)) = copyEmb p.1 (degEmb p.2) := by
            ext
            have h1 : (emb_swap (Fin.castAdd anc_sw (Fin.castAdd R k))).1 = k.1 := rfl
            have h2 : k.1 = p.2.1 + m_reg * p.1.1 := by
              have h3 := congrArg Fin.val hpair
              simpa [p, finProdFinEquiv] using h3
            have h3 := copyEmb53_deg_val R m_reg a anc_copy anc_sw hR1 hm_reg p.1 p.2
            change (emb_swap _).1 = (copyEmb53 hR1 hm_reg p.1 ⟨p.2.1, _⟩).1
            rw [h1, h2, h3]
            ring
          rw [hidx_eq]
          rfl
        · rw [Function.comp_apply, Fin.append_left, Fin.append_right]
          have hidx_eq : emb_swap (Fin.castAdd anc_sw (Fin.natAdd (R * m_reg) j)) = Fin.natAdd m_reg (flag j) := by
            ext
            have hfl : (flag j).1 = (R - 1) * m_reg + j.1 := rfl
            change R * m_reg + j.1 = m_reg + (flag j).1
            rw [hfl]
            have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
              calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
                _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
                _ = R * m_reg := by congr 1; omega
            omega
          rw [hidx_eq]
      · rw [Function.comp_apply, Fin.append_right]
        have hidx_eq : emb_swap (Fin.natAdd ((R * m_reg) + R) l) = swapAncEmb l := by
          ext
          change (R * m_reg) + R + l.1 = (swapAncEmb53 hR1 hm_reg l).1
          simp [swapAncEmb53, wireEquiv53]
        rw [hidx_eq, hclean l]
    have hU_act : ∀ y : Qubits (m_reg + e), (∀ l : Fin anc_sw, y (swapAncEmb l) = false) →
        act (embedOp c_swap.unitary emb_swap) (ket y) = ket (σ y) := by
      intro y hy
      refine act_embedOp_ket_map c_swap.unitary emb_swap y 1 (blockSwapY y) ?_ |>.trans (by simp [σ])
      rw [one_smul, hcomp_swap y hy]
      exact B.firstHitSwap_act R m_reg (blocksOf y) (flagsOf y)
    have hσ_anc : ∀ y : Qubits (m_reg + e), ∀ l : Fin anc_sw, σ y (swapAncEmb l) = false := by
      intro y l
      have hidx_eq : swapAncEmb l = emb_swap (Fin.natAdd ((R * m_reg) + R) l) := by
        ext
        change (swapAncEmb53 hR1 hm_reg l).1 = (R * m_reg) + R + l.1
        simp [swapAncEmb53, wireEquiv53]
      dsimp only [σ]
      rw [hidx_eq, updateOn_apply]
      dsimp only [blockSwapY]
      rw [Fin.append_right]
    have hσ_flag : ∀ y : Qubits (m_reg + e), (∀ l, y (swapAncEmb l) = false) →
        ∀ j : Fin R, σ y (Fin.natAdd m_reg (flag j)) = y (Fin.natAdd m_reg (flag j)) := by
      intro y _ j
      have hidx_eq : Fin.natAdd m_reg (flag j) = emb_swap (Fin.castAdd anc_sw (Fin.natAdd (R * m_reg) j)) := by
        ext
        have hfl : (flag j).1 = (R - 1) * m_reg + j.1 := rfl
        change m_reg + (flag j).1 = R * m_reg + j.1
        rw [hfl]
        have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
          calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
            _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
            _ = R * m_reg := by congr 1; omega
        omega
      dsimp only [σ]
      conv_lhs => rw [hidx_eq, updateOn_apply]
      dsimp only [blockSwapY]
      rw [Fin.append_left, Fin.append_right]
    have hσ_deg : ∀ (y : Qubits (m_reg + e)) (j : Fin R) (i : Fin m_reg),
        σ y (copyEmb j (degEmb i)) = swappedBlocks53 (blocksOf y) (flagsOf y) j i := by
      intro y j i
      have hidx_eq : copyEmb j (degEmb i) = emb_swap (Fin.castAdd anc_sw (Fin.castAdd R (finProdFinEquiv (j, i)))) := by
        ext
        have h1 := copyEmb53_deg_val R m_reg a anc_copy anc_sw hR1 hm_reg j i
        have h2 : (finProdFinEquiv (j, i)).1 = i.1 + m_reg * j.1 := rfl
        change (copyEmb53 hR1 hm_reg j ⟨i.1, _⟩).1 = (finProdFinEquiv (j, i)).1
        rw [h1, h2]; ring
      dsimp only [σ]
      rw [hidx_eq, updateOn_apply]
      dsimp only [blockSwapY]
      rw [Fin.append_left, Fin.append_left]
      dsimp only [flatReg]
      rw [finProdFinEquiv.symm_apply_apply]
    have hσσ : ∀ y : Qubits (m_reg + e), (∀ l, y (swapAncEmb l) = false) →
        (∀ l, σ y (swapAncEmb l) = false) ∧ σ (σ y) = y := by
      intro y hy
      refine ⟨hσ_anc y, ?_⟩
      funext w
      by_cases hmem : w ∈ Set.range emb_swap
      · obtain ⟨u, rfl⟩ := hmem
        refine Fin.addCases (fun u₁ => ?_) (fun l => ?_) u
        · refine Fin.addCases (fun k => ?_) (fun j => ?_) u₁
          · let p := finProdFinEquiv.symm k
            have hk_eq : k = finProdFinEquiv p := (finProdFinEquiv.apply_symm_apply k).symm
            have hw_eq : emb_swap (Fin.castAdd anc_sw (Fin.castAdd R k)) = copyEmb p.1 (degEmb p.2) := by
              ext
              have h1 : (emb_swap (Fin.castAdd anc_sw (Fin.castAdd R k))).1 = k.1 := rfl
              have h2 : k.1 = p.2.1 + m_reg * p.1.1 := by
                have h3 := congrArg Fin.val hk_eq
                simpa [p, finProdFinEquiv] using h3
              have h3 := copyEmb53_deg_val R m_reg a anc_copy anc_sw hR1 hm_reg p.1 p.2
              change (emb_swap _).1 = (copyEmb53 hR1 hm_reg p.1 ⟨p.2.1, _⟩).1
              rw [h1, h2, h3]; ring
            rw [hw_eq, hσ_deg]
            have hbl : blocksOf (σ y) = swappedBlocks53 (blocksOf y) (flagsOf y) := by
              funext j' i'; exact hσ_deg y j' i'
            have hfl : flagsOf (σ y) = flagsOf y := funext (hσ_flag y hy)
            rw [hbl, hfl, swappedBlocks53_invol]
          · have hw_eq : emb_swap (Fin.castAdd anc_sw (Fin.natAdd (R * m_reg) j)) = Fin.natAdd m_reg (flag j) := by
              ext
              have hfl : (flag j).1 = (R - 1) * m_reg + j.1 := rfl
              change R * m_reg + j.1 = m_reg + (flag j).1
              rw [hfl]
              have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
                calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
                  _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
                  _ = R * m_reg := by congr 1; omega
              omega
            rw [hw_eq, hσ_flag (σ y) (hσ_anc y) j, hσ_flag y hy j]
        · have hw_eq : emb_swap (Fin.natAdd ((R * m_reg) + R) l) = swapAncEmb l := by
            ext
            change (R * m_reg) + R + l.1 = (swapAncEmb53 hR1 hm_reg l).1
            simp [swapAncEmb53, wireEquiv53]
          rw [hw_eq, hσ_anc (σ y) l, hy l]
      · dsimp only [σ]
        rw [updateOn_off emb_swap (updateOn emb_swap y (blockSwapY y)) _ hmem,
          updateOn_off emb_swap y _ hmem]
    have hclean_indep : ∀ (x₁ x₂ : Qubits m_reg) (s : Qubits e),
        (∀ l, Fin.append x₁ s (swapAncEmb l) = false) ↔
          (∀ l, Fin.append x₂ s (swapAncEmb l) = false) := by
      intro x₁ x₂ s
      have hge : ∀ l : Fin anc_sw, m_reg ≤ (swapAncEmb l).1 :=
        fun l => swapAncEmb53_ge R m_reg a anc_copy anc_sw hR1 hm_reg l
      have happ : ∀ (x : Qubits m_reg) (l : Fin anc_sw),
          Fin.append x s (swapAncEmb l) =
            s ⟨(swapAncEmb l).1 - m_reg, by have := (swapAncEmb l).isLt; have := hge l; omega⟩ := fun x l => by
        have h1 : swapAncEmb l = Fin.natAdd m_reg
            ⟨(swapAncEmb l).1 - m_reg, by have := (swapAncEmb l).isLt; have := hge l; omega⟩ := by
          ext; simp; have := hge l; omega
        conv_lhs => rw [h1, Fin.append_right]
      simp_rw [happ]
    have hσ_tail_indep : ∀ (x : Qubits m_reg) (s : Qubits e) (j : Fin R)
        (k : Fin M_copy), m_reg ≤ k.1 →
        σ (Fin.append x s) (copyEmb j k) = σ (Fin.append (fun _ => false) s) (copyEmb j k) := by
      intro x s j k hk
      by_cases hkW : k.1 = W
      · have hk_eq : k = flagIdx := Fin.ext hkW
        rw [hk_eq, ← hflag_eq j]
        have hc1 : ∀ x' : Qubits m_reg, ∀ l : Fin anc_sw, Fin.append x' s (swapAncEmb l) = false → True := fun _ _ _ => trivial
        have hsf_x : σ (Fin.append x s) (Fin.natAdd m_reg (flag j)) = s (flag j) := by
          have hidx_eq : Fin.natAdd m_reg (flag j) = emb_swap (Fin.castAdd anc_sw (Fin.natAdd (R * m_reg) j)) := by
            ext
            have hfl : (flag j).1 = (R - 1) * m_reg + j.1 := rfl
            change m_reg + (flag j).1 = R * m_reg + j.1
            rw [hfl]
            have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
              calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
                _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
                _ = R * m_reg := by congr 1; omega
            omega
          dsimp only [σ]; rw [hidx_eq, updateOn_apply]; dsimp only [blockSwapY]
          rw [Fin.append_left, Fin.append_right]; dsimp only [flagsOf]; rw [Fin.append_right]
        have hsf_0 : σ (Fin.append (fun _ => false) s) (Fin.natAdd m_reg (flag j)) = s (flag j) := by
          have hidx_eq : Fin.natAdd m_reg (flag j) = emb_swap (Fin.castAdd anc_sw (Fin.natAdd (R * m_reg) j)) := by
            ext
            have hfl : (flag j).1 = (R - 1) * m_reg + j.1 := rfl
            change m_reg + (flag j).1 = R * m_reg + j.1
            rw [hfl]
            have hRm : m_reg + (R - 1) * m_reg = R * m_reg := by
              calc m_reg + (R - 1) * m_reg = 1 * m_reg + (R - 1) * m_reg := by rw [one_mul]
                _ = (1 + (R - 1)) * m_reg := (Nat.add_mul 1 (R - 1) m_reg).symm
                _ = R * m_reg := by congr 1; omega
            omega
          dsimp only [σ]; rw [hidx_eq, updateOn_apply]; dsimp only [blockSwapY]
          rw [Fin.append_left, Fin.append_right]; dsimp only [flagsOf]; rw [Fin.append_right]
        rw [hsf_x, hsf_0]
      · have hge : (R * m_reg) + R + anc_sw ≤ (copyEmb j k).1 :=
          copyEmb53_ge_of_tail R m_reg a anc_copy anc_sw hR1 hm_reg j k hk hkW
        have hnot : copyEmb j k ∉ Set.range emb_swap := by
          rintro ⟨u, hu⟩
          have hv := congrArg Fin.val hu
          change u.1 = (copyEmb j k).1 at hv
          have := u.isLt
          omega
        dsimp only [σ]
        rw [updateOn_off emb_swap _ _ hnot, updateOn_off emb_swap _ _ hnot]
        have hge_m : m_reg ≤ (copyEmb j k).1 := by
          have := Nat.le_mul_of_pos_left m_reg hR1
          omega
        have hlt_c := (copyEmb j k).isLt
        have hc_eq : copyEmb j k = Fin.natAdd m_reg ⟨(copyEmb j k).1 - m_reg, by omega⟩ := by
          ext; simp; omega
        rw [hc_eq, Fin.append_right, Fin.append_right]
    have hτ_swap_good : ∀ (x : Qubits m_reg) (s : Qubits e)
        (hs : ∃ j : Fin R, s (flag j) = true),
        (∀ l, Fin.append x s (swapAncEmb l) = false) →
        let j0 := firstHitMin (s ∘ flag) hs
        (σ (Fin.append x s) ∘ copyEmb j0 =
          updateOn degEmb (σ (Fin.append (fun _ => false) s) ∘ copyEmb j0) x) ∧
        (∀ j : Fin R, j ≠ j0 →
          σ (Fin.append x s) ∘ copyEmb j = σ (Fin.append (fun _ => false) s) ∘ copyEmb j) := by
      intro x s hs _ j0
      have hs' : ∃ j : Fin R, (s ∘ flag) j = true := hs
      have hfl_eq : ∀ x' : Qubits m_reg, flagsOf (Fin.append x' s) = s ∘ flag := fun x' => by
        funext j; dsimp only [flagsOf]; rw [Function.comp_apply, Fin.append_right]
      have hbl_0 : ∀ x' : Qubits m_reg, blocksOf (Fin.append x' s) ⟨0, hR1⟩ = x' := fun x' => by
        funext i; dsimp only [blocksOf]
        have hc0 : copyEmb ⟨0, hR1⟩ (degEmb i) = Fin.castAdd e i :=
          (copyEmb53_castAdd0 hR1 hm_reg i).symm
        rw [hc0, Fin.append_left]
      have hbl_pos : ∀ (x' : Qubits m_reg) (j : Fin R), j ≠ ⟨0, hR1⟩ →
          blocksOf (Fin.append x' s) j = blocksOf (Fin.append (fun _ => false) s) j := by
        intro x' j hj
        funext i
        have hj1 : 1 ≤ j.1 := Nat.pos_of_ne_zero fun h => hj (Fin.ext h)
        have hval := copyEmb53_deg_val R m_reg a anc_copy anc_sw hR1 hm_reg j i
        have hge : m_reg ≤ (copyEmb j (degEmb i)).1 := by
          change m_reg ≤ (copyEmb53 hR1 hm_reg j ⟨i.1, _⟩).1
          rw [hval]
          have h1 := Nat.le_mul_of_pos_left m_reg hj1
          omega
        have hlt_c := (copyEmb j (degEmb i)).isLt
        have hc_eq : copyEmb j (degEmb i) = Fin.natAdd m_reg ⟨(copyEmb j (degEmb i)).1 - m_reg, by omega⟩ := by
          ext; simp; omega
        dsimp only [blocksOf]
        rw [hc_eq, Fin.append_right, Fin.append_right]
      constructor
      · funext k
        by_cases hk : k.1 < m_reg
        · have hk_eq : k = degEmb ⟨k.1, hk⟩ := Fin.ext rfl
          rw [hk_eq, Function.comp_apply, hσ_deg, hfl_eq x, updateOn_apply,
            swappedBlocks53_eq_swap _ _ hs', circuits_firstTrue53_eq]
          change blocksOf (Fin.append x s) (Equiv.swap ⟨0, _⟩ j0 j0) ⟨k.1, hk⟩ = x ⟨k.1, hk⟩
          rw [Equiv.swap_apply_right, hbl_0]
        · have hnot : k ∉ Set.range degEmb := by
            rintro ⟨i, hi⟩; have := congrArg Fin.val hi; change i.1 = k.1 at this; omega
          rw [Function.comp_apply, updateOn_off degEmb _ _ hnot, Function.comp_apply]
          exact hσ_tail_indep x s j0 k (by omega)
      · intro j hj
        funext k
        by_cases hk : k.1 < m_reg
        · have hk_eq : k = degEmb ⟨k.1, hk⟩ := Fin.ext rfl
          rw [hk_eq, Function.comp_apply, Function.comp_apply, hσ_deg, hσ_deg,
            hfl_eq x, hfl_eq (fun _ => false),
            swappedBlocks53_eq_swap _ _ hs', swappedBlocks53_eq_swap _ _ hs',
            circuits_firstTrue53_eq]
          let j' := Equiv.swap (⟨0, (QuantumLTF.Membership.Supplement.firstTrue53 (s ∘ flag) hs').pos⟩ : Fin R) j0 j
          have hj'_ne0 : j' ≠ ⟨0, hR1⟩ := by
            intro h0
            have h0' : Equiv.swap (⟨0, (QuantumLTF.Membership.Supplement.firstTrue53 (s ∘ flag) hs').pos⟩ : Fin R) j0 j =
                Equiv.swap (⟨0, (QuantumLTF.Membership.Supplement.firstTrue53 (s ∘ flag) hs').pos⟩ : Fin R) j0 j0 := by
              rw [Equiv.swap_apply_right]; exact Fin.ext (congrArg Fin.val h0)
            exact hj ((Equiv.swap _ _).injective h0')
          change blocksOf (Fin.append x s) j' ⟨k.1, hk⟩ =
            blocksOf (Fin.append (fun _ => false) s) j' ⟨k.1, hk⟩
          rw [hbl_pos x j' hj'_ne0]
        · exact hσ_tail_indep x s j k (by omega)
    have hR_prob : (1 - (3 / 100 : ℝ)) ^ R ≤ ξ ^ 2 / 16 :=
      amplification_R_prob (q1 := 3 / 100) le_rfl (by norm_num) hξ0 hξ1
    have hpar := parallel_grover_swap (wireEquiv53 hR1 hm_reg) copyEmb swapAncEmb
      (fun j i => Equiv.apply_symm_apply _ _)
      (fun l => Equiv.apply_symm_apply _ _)
      degEmb flagIdx flag hflag_eq φ_copy hφ_norm Ft hFt_norm β_copy hφ_fac hβ_indep
      ψ_pre hψ_pre_norm hψ_pre_eq (embedOp c_swap.unitary emb_swap) σ σ
      hU_act hσσ hσσ hσ_flag hτ_swap_good hclean_indep
      (3 / 100) (by norm_num) hq1_lo ξ hξ0 hξ1 hR_prob
    have hψ_eq : act (c.unitary fun _ => A) (zeroKet (m_reg + e)) =
        act (embedOp c_swap.unitary emb_swap) ψ_pre := by
      dsimp only [c, ψ_pre]
      rw [oracleCircuit_unitary_append, oracleCircuit_unitary_lift, embedCircuit_unitary, act_mul]
    rw [← hψ_eq] at hpar
    rcases hpar with ⟨hpar1, χ, hχ_norm, hpar_fac⟩
    refine ⟨by convert hpar1, Ft, χ, hFt_norm, hχ_norm, hFt_err, fun x s hs => by convert hpar_fac x s hs⟩

end GroverParallel53

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n K D q a : ℕ) (ξ : ℝ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q → 0 < ξ → ξ < 1 / 2 →
        ∃ (e r : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1 + a) (n * q + e))
          (flag : Fin r ↪ Fin e) (good : Set (Qubits r)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) ∧
          (c.gateCount : ℝ) ≤ C * (K : ℝ) ^ (1 / 4 : ℝ) * Real.log (1 / ξ) *
            (n * (Real.log (2 ^ q) + Real.log (n * D)) + a) ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ A : Matrix (Qubits (n * q + 1 + a)) (Qubits (n * q + 1 + a)) ℂ,
            A ∈ Matrix.unitaryGroup (Qubits (n * q + 1 + a)) ℂ →
          ∀ F0 Fw : EuclideanSpace ℂ (Qubits (n * q + a)),
            (∀ (x : Qubits (n * q)) (y : Bool) (s : Qubits a),
              act A (zeroKet (n * q + 1 + a)) (Fin.append (Fin.snoc (α := fun _ => Bool) x y) s) =
                (1 / Real.sqrt 2 : ℂ) * (if y then Fw (Fin.append x s) else F0 (Fin.append x s))) →
            projDist n q a D w Fw ≤ ξ * Real.sqrt (bandWeight w K) / 4 →
            open Classical in
            let ψ := act (c.unitary fun _ => A) (zeroKet (n * q + e))
            let P := probEvent ψ (fun z => (fun j : Fin e => z (Fin.natAdd (n * q) j)) ∘ flag ∈ good)
            1 - ξ ^ 2 / 16 ≤ P ∧
            ∃ (Ft : EuclideanSpace ℂ (Qubits (n * q))) (χ : EuclideanSpace ℂ (Qubits e)),
              ‖Ft‖ = 1 ∧ ‖χ‖ = 1 ∧ ‖Ft - bandKet n q K w‖ ≤ ξ ∧
              ∀ (x : Qubits (n * q)) (s : Qubits e), s ∘ flag ∈ good →
                ψ (Fin.append x s) = (Real.sqrt P : ℂ) * Ft x * χ s := by
  obtain ⟨c_band, hc_band, hp_bds, hbw_eq⟩ := hermite_band_bounds_53.1
  obtain ⟨B⟩ := band_circuits_53
  let C_circ : ℝ := max 1 B.C_circ
  let C_q : ℝ := max 1 (Real.pi / 2 * Real.sqrt (2 / c_band))
  let C_R : ℝ := 6 / Real.log (100 / 97) + 3 / Real.log 2
  let C_tot : ℝ := max (C_R * C_q) ((8 * C_circ / Real.log 2) * C_R * C_q)
  have hlog97 : 0 < Real.log (100 / 97 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_R : 0 < C_R := by dsimp [C_R]; positivity
  have hC_q : 1 ≤ C_q := le_max_left _ _
  have hCtot_pos : 0 < C_tot := by
    dsimp [C_tot]; exact lt_max_of_lt_left (mul_pos hC_R (by linarith))
  refine ⟨C_tot, hCtot_pos, fun n K D q a ξ hK hD hq hξ0 hξ1 => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨e, r, c, flag, good, h_un, hq_c, hg_c, hfalse⟩ :=
      GroverParallel53.theorem_5_3_n_zero (D := D) (q := q) (a := a) hCtot_pos hK hξ0 hξ1
    exact ⟨e, r, c, flag, good, h_un, hq_c, by simpa using hg_c, fun w hw _ _ _ _ _ _ => False.elim (hfalse w hw)⟩
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    exact GroverParallel53.theorem_5_3_n_pos B hc_band hp_bds hbw_eq hn1 hK hD hq hξ0 hξ1
