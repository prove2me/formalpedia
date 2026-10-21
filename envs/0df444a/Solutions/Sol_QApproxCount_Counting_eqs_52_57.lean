-- Prove2me | solution 1 for QApproxCount.Counting.eqs_52_57
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:26:06.204816+00:00
-- url     : https://prove2.me/submissions/bcaf176f-e206-46c7-9a52-3134f5069216

import Mathlib
import Definitions.Def_QApproxCount_Counting_Algorithm
set_option autoImplicit false

open QApproxCount.Counting

lemma rot_core (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ)
    (hmax : θmax = (1 + γ) * θmin) :
    |(rotK θmin θmax : ℝ) - 1 / (2 * γ)| ≤ 1 / 2 ∧
      |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ θmin := by
  have hK : θmin / (2 * (θmax - θmin)) = 1 / (2 * γ) := by
    have h1 := hγ.ne'
    have h2 := hθmin.ne'
    rw [hmax, show (1 + γ) * θmin - θmin = γ * θmin by ring]; field_simp
  constructor
  · have h := abs_sub_round (θmin / (2 * (θmax - θmin)))
    rw [hK] at h
    have e : (rotK θmin θmax : ℝ) = (round (1 / (2 * γ)) : ℝ) := by
      unfold rotK; rw [hK]
    rw [e, abs_sub_comm]; exact h
  · have hy := abs_sub_round ((Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2)
    have e : (rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ) =
        2 * θmin * ((round ((Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2) : ℝ) -
          (Real.pi * (rotK θmin θmax : ℝ) / θmin - 1) / 2) := by
      unfold rotR
      push_cast
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * θmin), abs_sub_comm]
    nlinarith

lemma sin_sq_shift (x : ℝ) (k : ℤ) : Real.sin (x + k * Real.pi) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_add_int_mul_pi, mul_pow]
  rcases Int.even_or_odd k with h | h <;> simp [h.neg_one_zpow]

/-- facts about k and r. -/
lemma rot_facts (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002) :
    0.5 - γ / 2 ≤ γ * (rotK θmin θmax : ℝ) ∧ γ * (rotK θmin θmax : ℝ) ≤ 0.5 + γ / 2 ∧
    (1 + γ) * θmin ≤ 0.002 ∧
    |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ θmin ∧
    0 < (rotR θmin θmax : ℝ) := by
  obtain ⟨h1, h2⟩ := rot_core θmin θmax γ hθmin hγ hmax
  have hk := abs_le.mp h1
  have hγk : γ * (1 / (2 * γ)) = 1 / 2 := by field_simp
  have hA : 0.5 - γ / 2 ≤ γ * (rotK θmin θmax : ℝ) := by
    have := mul_le_mul_of_nonneg_left hk.1 hγ.le
    nlinarith
  have hB : γ * (rotK θmin θmax : ℝ) ≤ 0.5 + γ / 2 := by
    have := mul_le_mul_of_nonneg_left hk.2 hγ.le
    nlinarith
  have hθ : (1 + γ) * θmin ≤ 0.002 := by rw [← hmax]; exact hθmax
  refine ⟨hA, hB, hθ, h2, ?_⟩
  have hkpos : (0 : ℝ) < (rotK θmin θmax : ℝ) := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hk1 : (1 : ℝ) ≤ (rotK θmin θmax : ℝ) := by
    have : (0 : ℤ) < rotK θmin θmax := by exact_mod_cast hkpos
    exact_mod_cast this
  have hd := (abs_le.mp h2).1
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  have hpi := Real.pi_gt_three
  have : 0 < (rotR θmin θmax : ℝ) * θmin := by nlinarith
  exact pos_of_mul_pos_left this hθmin.le

theorem solution (θmin θmax γ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002) :
    |(rotR θmin θmax : ℝ) * θmin - Real.pi * (rotK θmin θmax : ℝ)| ≤ 0.002 ∧
      |(rotR θmin θmax : ℝ) * θmax - (Real.pi * (rotK θmin θmax : ℝ) + Real.pi / 2)| ≤ 1.102 := by
  obtain ⟨hA, hB, hθ, hd, hr⟩ := rot_facts θmin θmax γ hθmin hγ hγ1 hmax hθmax
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  set k : ℝ := (rotK θmin θmax : ℝ) with hk
  set r : ℝ := (rotR θmin θmax : ℝ) with hr'
  set d : ℝ := r * θmin - Real.pi * k with hd'
  have hdb := abs_le.mp hd
  constructor
  · rw [abs_le]; constructor <;> linarith
  · have e : r * θmax - (Real.pi * k + Real.pi / 2) = (1 + γ) * d + Real.pi * (γ * k - 1 / 2) := by
      rw [hmax, hd']; ring
    rw [e]
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have h1 : (1 + γ) * d ≤ (1 + γ) * θmin := mul_le_mul_of_nonneg_left hdb.2 (by linarith)
    have h2 : -((1 + γ) * θmin) ≤ (1 + γ) * d := by
      have := mul_le_mul_of_nonneg_left hdb.1 (by linarith : (0:ℝ) ≤ 1 + γ)
      linarith
    have h3 : Real.pi * (γ * k - 1 / 2) ≤ Real.pi * (γ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hpi0.le
    have h4 : -(Real.pi * (γ / 2)) ≤ Real.pi * (γ * k - 1 / 2) := by
      have := mul_le_mul_of_nonneg_left (by linarith : -(γ / 2) ≤ γ * k - 1 / 2) hpi0.le
      linarith
    have h5 : Real.pi * γ ≤ 3.1416 * 0.7 :=
      mul_le_mul hpi.le hγ1 hγ.le (by norm_num)
    rw [abs_le]; constructor <;> nlinarith
