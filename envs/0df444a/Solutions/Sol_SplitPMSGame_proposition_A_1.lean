-- Prove2me | solution 1 for SplitPMSGame.proposition_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:42:24.650948+00:00
-- url     : https://prove2.me/submissions/ff08af07-7496-4aec-92b5-9cb79a6d7b4e

import Mathlib
import Definitions.Def_SplitPMSGame_unitGame

open Filter Topology

open SplitPMSGame in
theorem solution :
    (∀ u : ℕ, 1 ≤ u →
        StrictAntiOn (fun z : ℕ => beta1 z u) {z | 1 ≤ z} ∧
          Tendsto (fun z : ℕ => beta1 z u) atTop (𝓝 0)) ∧
      (∀ u : ℕ, 1 ≤ u → beta2 1 u = 1 / 2) ∧
      (∀ z : ℕ, 2 ≤ z →
        StrictMonoOn (fun u : ℕ => beta2 z u) {u | 1 ≤ u} ∧
          Tendsto (fun u : ℕ => beta2 z u) atTop (𝓝 (1 / 2))) := by
  refine ⟨fun u hu => ⟨?_, ?_⟩, fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hab' : (a:ℝ) < b := by exact_mod_cast hab
    have hu' : (1:ℝ) ≤ u := by exact_mod_cast hu
    show beta1 b u < beta1 a u
    unfold beta1
    have hDa : 0 < 2 * ((u:ℝ) + a) * ((u:ℝ) + a - 1) :=
      mul_pos (mul_pos two_pos (by linarith)) (by linarith)
    have hDb : 0 < 2 * ((u:ℝ) + b) * ((u:ℝ) + b - 1) :=
      mul_pos (mul_pos two_pos (by linarith)) (by linarith)
    rw [div_lt_div_iff₀ hDb hDa]
    have hbr : 0 < ((u:ℝ) - 1) * ((a:ℝ) + b - 1) + 2 * a * b := by nlinarith
    nlinarith [mul_pos (mul_pos (show (0:ℝ) < u + 1 by linarith) (sub_pos.mpr hab')) hbr]
  · have hu' : (1:ℝ) ≤ u := by exact_mod_cast hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat ((u:ℝ) + 1)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with z hz1
      have hz' : (1:ℝ) ≤ z := by exact_mod_cast hz1
      unfold beta1
      apply div_nonneg
      · nlinarith
      · exact (mul_pos (mul_pos two_pos (by linarith)) (by linarith)).le
    · filter_upwards [eventually_ge_atTop 1] with z hz1
      have hz' : (1:ℝ) ≤ z := by exact_mod_cast hz1
      unfold beta1
      have hD : 0 < 2 * ((u:ℝ) + z) * ((u:ℝ) + z - 1) :=
        mul_pos (mul_pos two_pos (by linarith)) (by linarith)
      rw [div_le_div_iff₀ hD (by linarith)]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ u + 1 by linarith)
        (show (0:ℝ) ≤ 2 * u * (u - 1) + z * (3 * u - 1) by nlinarith)]
  · have hu' : (1:ℝ) ≤ u := by exact_mod_cast hu
    unfold beta2
    rw [div_eq_iff (by push_cast; intro h; nlinarith)]
    push_cast
    ring
  · have hz' : (2:ℝ) ≤ z := by exact_mod_cast hz
    intro a ha b hb hab
    simp only [Set.mem_setOf_eq] at ha hb
    have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
    have hab' : (a:ℝ) < b := by exact_mod_cast hab
    show beta2 z a < beta2 z b
    unfold beta2
    have hDa : 0 < 2 * ((a:ℝ) + z) * ((a:ℝ) + z - 1) :=
      mul_pos (mul_pos two_pos (by linarith)) (by linarith)
    have hDb : 0 < 2 * ((b:ℝ) + z) * ((b:ℝ) + z - 1) :=
      mul_pos (mul_pos two_pos (by linarith)) (by linarith)
    rw [div_lt_div_iff₀ hDa hDb]
    have hK : 0 < (z:ℝ) * ((z:ℝ) - 1) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos hK (mul_pos (sub_pos.mpr hab') (show (0:ℝ) < a + b + 2 * z - 1 by linarith))]
  · have hz' : (2:ℝ) ≤ z := by exact_mod_cast hz
    have hK : 0 ≤ (z:ℝ) * ((z:ℝ) - 1) / 2 := by
      apply div_nonneg _ (by norm_num); exact mul_nonneg (by linarith) (by linarith)
    have hlim : Tendsto (fun u : ℕ => 1 / 2 - ((z:ℝ) * ((z:ℝ) - 1) / 2) / (u:ℝ)) atTop
        (𝓝 (1 / 2)) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat ((z:ℝ) * ((z:ℝ) - 1) / 2))
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with u hu1
      have hu' : (1:ℝ) ≤ u := by exact_mod_cast hu1
      show 1 / 2 - ((z:ℝ) * ((z:ℝ) - 1) / 2) / (u:ℝ) ≤ beta2 z u
      unfold beta2
      have hP1 : (u:ℝ) + z ≠ 0 := by linarith
      have hP2 : (u:ℝ) + z - 1 ≠ 0 := by linarith
      have e : (u:ℝ) * ((u:ℝ) + 2 * z - 1) / (2 * ((u:ℝ) + z) * ((u:ℝ) + z - 1)) =
          1 / 2 - ((z:ℝ) * ((z:ℝ) - 1) / 2) / (((u:ℝ) + z) * ((u:ℝ) + z - 1)) := by
        first | (field_simp; ring) | field_simp
      rw [e]
      have hle : (u:ℝ) ≤ ((u:ℝ) + z) * ((u:ℝ) + z - 1) := by nlinarith
      have := div_le_div_of_nonneg_left hK (by linarith : (0:ℝ) < u) hle
      linarith
    · filter_upwards [eventually_ge_atTop 1] with u hu1
      have hu' : (1:ℝ) ≤ u := by exact_mod_cast hu1
      show beta2 z u ≤ 1 / 2
      unfold beta2
      have hD : 0 < 2 * ((u:ℝ) + z) * ((u:ℝ) + z - 1) :=
        mul_pos (mul_pos two_pos (by linarith)) (by linarith)
      rw [div_le_div_iff₀ hD (by norm_num)]
      nlinarith [show (0:ℝ) ≤ (z:ℝ) * ((z:ℝ) - 1) by nlinarith]
