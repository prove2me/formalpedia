-- Prove2me | solution 1 for Plasticity.U16.two_direction
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:09:02.502207+00:00
-- url     : https://prove2.me/submissions/842ddffa-7ad6-40e5-9c64-55598af00616

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module
import Theorems.Thm_Plasticity_U16_basic_estimate
import Theorems.Thm_Plasticity_Aux_window_avg_three_point

namespace Sol_Plasticity_U16_two_direction

/-- The two-parameter profile `(s, r) ↦ ‖p + s • v + r • w‖` is `1`-Lipschitz in each
variable when `‖v‖, ‖w‖ ≤ 1`. -/
lemma profile_lip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p v w : X) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (s r s' r' : ℝ) :
    |‖p + s • v + r • w‖ - ‖p + s' • v + r' • w‖| ≤ |s - s'| + |r - r'| := by
  calc |‖p + s • v + r • w‖ - ‖p + s' • v + r' • w‖|
      ≤ ‖(p + s • v + r • w) - (p + s' • v + r' • w)‖ := abs_norm_sub_norm_le _ _
    _ = ‖(s - s') • v + (r - r') • w‖ := by congr 1; module
    _ ≤ ‖(s - s') • v‖ + ‖(r - r') • w‖ := norm_add_le _ _
    _ = |s - s'| * ‖v‖ + |r - r'| * ‖w‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |s - s'| * 1 + |r - r'| * 1 := by
      gcongr
    _ = |s - s'| + |r - r'| := by ring

end Sol_Plasticity_U16_two_direction

open Sol_Plasticity_U16_two_direction in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (v w : X) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    ‖F (t • v) + F (t • w) + F (-(t • (v + w)))‖ ≤ 96 * t ^ 2 := by
  set D : Y := F (t • v) + F (t • w) + F (-(t • (v + w))) with hDdef
  by_cases hD0 : D = 0
  · rw [hD0, norm_zero]
    positivity
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  -- The three-point family with unit weights.
  set c : Fin 3 → ℝ := fun _ => 1 with hc
  set x : Fin 3 → X := ![t • v, t • w, -(t • (v + w))] with hx
  have hsum : ∑ i, c i • F (x i) = D := by
    simp [hc, hx, Fin.sum_univ_three, hDdef]
  have hcnn : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ c i := by
    intro i _
    simp [hc]
  have hxmem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), x i ∈ Metric.closedBall (0 : X) 1 := by
    intro i _
    rw [mem_closedBall_zero_iff]
    fin_cases i
    · show ‖t • v‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      nlinarith [norm_nonneg v]
    · show ‖t • w‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      nlinarith [norm_nonneg w]
    · show ‖-(t • (v + w))‖ ≤ 1
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := norm_add_le v w
      nlinarith [norm_nonneg (v + w)]
  -- A preimage of the unit vector opposite to `D`.
  have hunit : -(‖D‖⁻¹ • D) ∈ Metric.sphere (0 : Y) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hDpos.ne']
  obtain ⟨a, ha, hFa⟩ := hcover hunit
  have ha1 : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha
  -- The two-parameter profile through `(7/8) a`.
  set g : ℝ → ℝ → ℝ := fun s r => ‖(7 / 8 : ℝ) • a + s • v + r • w‖ with hg
  have hglip : ∀ s r s' r' : ℝ, |g s r - g s' r'| ≤ |s - s'| + |r - r'| :=
    profile_lip _ v w hv hw
  have hK : ∀ s ∈ Set.Icc (-(1 / 16 : ℝ)) (1 / 16), ∀ r ∈ Set.Icc (-(1 / 16 : ℝ)) (1 / 16),
      ‖D‖ / 2 ≤ g (s - t) r + g s (r - t) + g (s + t) (r + t) - 3 * g s r := by
    intro s hs r hr
    have hs' : |s| ≤ 1 / 16 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hr' : |r| ≤ 1 / 16 := abs_le.mpr ⟨hr.1, hr.2⟩
    have hsv : ‖s • v‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg s, norm_nonneg v]
    have hrw : ‖r • w‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg r, norm_nonneg w]
    set b : X := (7 / 8 : ℝ) • a + s • v + r • w with hb
    have hbmem : b ∈ Metric.closedBall (0 : X) 1 := by
      rw [mem_closedBall_zero_iff]
      have h78 : ‖(7 / 8 : ℝ) • a‖ = 7 / 8 * ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 8)]
      calc ‖b‖ ≤ ‖(7 / 8 : ℝ) • a + s • v‖ + ‖r • w‖ := norm_add_le _ _
        _ ≤ ‖(7 / 8 : ℝ) • a‖ + ‖s • v‖ + ‖r • w‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ 1 := by rw [h78]; nlinarith
    have hba : ‖b - a‖ ≤ 1 / 4 := by
      have e : b - a = (-(1 / 8 : ℝ)) • a + s • v + r • w := by rw [hb]; module
      have h18 : ‖(-(1 / 8 : ℝ)) • a‖ = 1 / 8 * ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs]; norm_num
      rw [e]
      calc ‖(-(1 / 8 : ℝ)) • a + s • v + r • w‖
          ≤ ‖(-(1 / 8 : ℝ)) • a + s • v‖ + ‖r • w‖ := norm_add_le _ _
        _ ≤ ‖(-(1 / 8 : ℝ)) • a‖ + ‖s • v‖ + ‖r • w‖ := by
          gcongr; exact norm_add_le _ _
        _ ≤ 1 / 4 := by rw [h18]; nlinarith
    have hFa' : F a = -(‖∑ i, c i • F (x i)‖⁻¹ • ∑ i, c i • F (x i)) := by
      rw [hsum]; exact hFa
    have hD' : ∑ i, c i • F (x i) ≠ 0 := by rw [hsum]; exact hD0
    have key := Plasticity.U16.basic_estimate F hmaps hlip hsphere hcover Finset.univ c x
      hcnn hxmem hD' a ha hFa' b hbmem hba
    rw [hsum] at key
    have e0 : ‖b - x 0‖ = g (s - t) r := by
      show ‖b - t • v‖ = ‖(7 / 8 : ℝ) • a + (s - t) • v + r • w‖
      congr 1; rw [hb]; module
    have e1 : ‖b - x 1‖ = g s (r - t) := by
      show ‖b - t • w‖ = ‖(7 / 8 : ℝ) • a + s • v + (r - t) • w‖
      congr 1; rw [hb]; module
    have e2 : ‖b - x 2‖ = g (s + t) (r + t) := by
      show ‖b - -(t • (v + w))‖ = ‖(7 / 8 : ℝ) • a + (s + t) • v + (r + t) • w‖
      congr 1; rw [hb]; module
    have e3 : ‖b‖ = g s r := rfl
    simp only [Fin.sum_univ_three, hc, one_mul, e0, e1, e2, e3] at key
    linarith
  have hwin := Plasticity.Aux.window_avg_three_point g hglip (1 / 16) t (‖D‖ / 2)
    (by norm_num) ht0.le hK
  have h48 : 3 * t ^ 2 / (1 / 16 : ℝ) = 48 * t ^ 2 := by ring
  rw [h48] at hwin
  linarith
