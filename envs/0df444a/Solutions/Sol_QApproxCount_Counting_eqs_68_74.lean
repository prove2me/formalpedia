-- Prove2me | solution 1 for QApproxCount.Counting.eqs_68_74
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:32:05.797915+00:00
-- url     : https://prove2.me/submissions/26a80737-102a-4b39-a892-cc49eae86d5b

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

lemma sin_lb (x : ℝ) (h1 : 0.42 ≤ x) (h2 : x ≤ 2.68) : 0.4076 ≤ Real.sin x := by
  have hpi := Real.pi_gt_d4
  have hpi2 : Real.pi / 2 ≤ Real.pi - 0.42 := by linarith
  have h0 : 0.4076 ≤ Real.sin 0.42 := by
    have := Real.sin_gt_sub_cube (x := 0.42) (by norm_num)
    norm_num at this ⊢
    linarith
  rcases le_total x (Real.pi / 2) with h | h
  · refine h0.trans (Real.sin_le_sin_of_le_of_le_pi_div_two ?_ h h1)
    linarith [Real.pi_pos]
  · rw [← Real.sin_pi_sub]
    refine h0.trans (Real.sin_le_sin_of_le_of_le_pi_div_two ?_ ?_ ?_)
    · linarith [Real.pi_pos]
    · linarith
    · linarith

theorem solution (θmin θmax γ θ : ℝ) (hθmin : 0 < θmin) (hγ : 0 < γ) (hγ1 : γ ≤ 0.7)
    (hmax : θmax = (1 + γ) * θmin) (hθmax : θmax ≤ 0.002)
    (hlo : θmin * (1 + 0.9 * γ) ≤ θ) (hhi : θ ≤ θmax) :
    0.42 ≤ (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ∧
      (rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ) ≤ 2.68 ∧
      0.165 ≤ Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 := by
  obtain ⟨hA, hB, hθ, hd, hr⟩ := rot_facts θmin θmax γ hθmin hγ hγ1 hmax hθmax
  have hs : Real.sin ((rotR θmin θmax : ℝ) * θ) ^ 2 =
      Real.sin ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) ^ 2 := by
    rw [← sin_sq_shift ((rotR θmin θmax : ℝ) * θ - Real.pi * (rotK θmin θmax : ℝ)) (rotK θmin θmax)]
    congr 2; ring
  rw [hs]
  have hθ2 : θmin ≤ 0.002 := by nlinarith
  set k : ℝ := (rotK θmin θmax : ℝ) with hk
  set r : ℝ := (rotR θmin θmax : ℝ) with hr'
  set d : ℝ := r * θmin - Real.pi * k with hd'
  have hdb := abs_le.mp hd
  have hpi := Real.pi_lt_d4
  have hpi' := Real.pi_gt_d4
  have hpi0 := Real.pi_pos
  have hlow : 0.42 ≤ r * θ - Real.pi * k := by
    have h1 : r * (θmin * (1 + 0.9 * γ)) ≤ r * θ := mul_le_mul_of_nonneg_left hlo hr.le
    have h2 : d * (1 + 0.9 * γ) ≥ -(θmin * (1 + 0.9 * γ)) := by
      have := mul_le_mul_of_nonneg_right hdb.1 (by linarith : (0:ℝ) ≤ 1 + 0.9 * γ)
      linarith
    have h3 : Real.pi * (0.5 - γ / 2) ≤ Real.pi * (γ * k) :=
      mul_le_mul_of_nonneg_left hA hpi0.le
    have h4 : Real.pi * 0.15 ≤ Real.pi * (0.5 - γ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hpi0.le
    have e : r * (θmin * (1 + 0.9 * γ)) = (d + Real.pi * k) * (1 + 0.9 * γ) := by
      rw [hd']; ring
    nlinarith
  have hup : r * θ - Real.pi * k ≤ 2.68 := by
    have h1 : r * θ ≤ r * θmax := mul_le_mul_of_nonneg_left hhi hr.le
    have h2 : (1 + γ) * d ≤ (1 + γ) * θmin := mul_le_mul_of_nonneg_left hdb.2 (by linarith)
    have h3 : Real.pi * (γ * k) ≤ Real.pi * (0.5 + γ / 2) :=
      mul_le_mul_of_nonneg_left hB hpi0.le
    have h4 : Real.pi * γ ≤ 3.1416 * 0.7 := mul_le_mul hpi.le hγ1 hγ.le (by norm_num)
    have e : r * θmax = (1 + γ) * (d + Real.pi * k) := by rw [hmax, hd']; ring
    nlinarith
  refine ⟨hlow, hup, ?_⟩
  have := sin_lb _ hlow hup
  nlinarith
