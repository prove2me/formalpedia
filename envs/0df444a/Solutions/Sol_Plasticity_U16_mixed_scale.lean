-- Prove2me | solution 1 for Plasticity.U16.mixed_scale
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:08:21.051211+00:00
-- url     : https://prove2.me/submissions/f7520c5d-cd07-44bb-b867-60627847e939

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module
import Theorems.Thm_Plasticity_U16_basic_estimate
import Theorems.Thm_Plasticity_Aux_window_avg_two_point

namespace Sol_Plasticity_U16_mixed_scale

/-- The profile `σ ↦ ‖p + σ • v‖` along a unit direction is `1`-Lipschitz. -/
lemma profile_lip {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p v : X) (hv : ‖v‖ = 1) : LipschitzWith 1 (fun σ : ℝ => ‖p + σ • v‖) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  calc |‖p + x • v‖ - ‖p + y • v‖| ≤ ‖(p + x • v) - (p + y • v)‖ := abs_norm_sub_norm_le _ _
    _ = ‖(x - y) • v‖ := by congr 1; module
    _ = |x - y| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]

end Sol_Plasticity_U16_mixed_scale

open Sol_Plasticity_U16_mixed_scale in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (v : X) (hv : ‖v‖ = 1) (t u : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖t⁻¹ • F (t • v) + u⁻¹ • F (-(u • v))‖ ≤ 8 * (t + u) := by
  set D : Y := u • F (t • v) + t • F (-(u • v)) with hDdef
  have htu : 0 < t * u := mul_pos ht0 hu0
  have hrewrite : t⁻¹ • F (t • v) + u⁻¹ • F (-(u • v)) = (t * u)⁻¹ • D := by
    rw [hDdef, smul_add, smul_smul, smul_smul]
    congr 2 <;> field_simp
  rw [hrewrite, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htu]
  -- It suffices to show `‖D‖ ≤ 8 t u (t + u)`.
  suffices hD : ‖D‖ ≤ 8 * (t * u) * (t + u) by
    rw [inv_mul_le_iff₀ htu]
    linarith
  by_cases hD0 : D = 0
  · rw [hD0, norm_zero]
    positivity
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  -- The two-point family `c = (u, t)`, `x = (t v, -(u v))`.
  set c : Fin 2 → ℝ := ![u, t] with hc
  set x : Fin 2 → X := ![t • v, -(u • v)] with hx
  have hsum : ∑ i, c i • F (x i) = D := by
    simp [hc, hx, Fin.sum_univ_two, hDdef]
  have hcnn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ c i := by
    intro i _
    fin_cases i
    · simp [hc]; exact hu0.le
    · simp [hc]; exact ht0.le
  have hxmem : ∀ i ∈ (Finset.univ : Finset (Fin 2)), x i ∈ Metric.closedBall (0 : X) 1 := by
    intro i _
    fin_cases i
    · simp [hx, norm_smul, hv, abs_of_pos ht0]; exact ht1
    · simp [hx, norm_smul, hv, abs_of_pos hu0]; exact hu1
  -- A preimage of the unit vector opposite to `D`.
  have hunit : -(‖D‖⁻¹ • D) ∈ Metric.sphere (0 : Y) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hDpos.ne']
  obtain ⟨a, ha, hFa⟩ := hcover hunit
  have ha1 : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp ha
  -- The profile along `v` through `(7/8) a`.
  set g : ℝ → ℝ := fun σ => ‖(7 / 8 : ℝ) • a + σ • v‖ with hg
  have hglip : LipschitzWith 1 g := profile_lip _ v hv
  have hK : ∀ s ∈ Set.Icc (-(1 / 8 : ℝ)) (1 / 8),
      ‖D‖ / 2 ≤ u * g (s - t) + t * g (s + u) - (t + u) * g s := by
    intro s hs
    have hs' : |s| ≤ 1 / 8 := abs_le.mpr ⟨hs.1, hs.2⟩
    set b : X := (7 / 8 : ℝ) • a + s • v with hb
    have hbmem : b ∈ Metric.closedBall (0 : X) 1 := by
      rw [mem_closedBall_zero_iff]
      calc ‖b‖ ≤ ‖(7 / 8 : ℝ) • a‖ + ‖s • v‖ := norm_add_le _ _
        _ = 7 / 8 * ‖a‖ + |s| := by
          rw [norm_smul, norm_smul, hv, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 7 / 8)]
        _ ≤ 1 := by nlinarith
    have hba : ‖b - a‖ ≤ 1 / 4 := by
      have : b - a = (-(1 / 8 : ℝ)) • a + s • v := by rw [hb]; module
      rw [this]
      calc ‖(-(1 / 8 : ℝ)) • a + s • v‖ ≤ ‖(-(1 / 8 : ℝ)) • a‖ + ‖s • v‖ := norm_add_le _ _
        _ = 1 / 8 * ‖a‖ + |s| := by
          rw [norm_smul, norm_smul, hv, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
          norm_num
        _ ≤ 1 / 4 := by nlinarith
    have hFa' : F a = -(‖∑ i, c i • F (x i)‖⁻¹ • ∑ i, c i • F (x i)) := by
      rw [hsum]; exact hFa
    have hD' : ∑ i, c i • F (x i) ≠ 0 := by rw [hsum]; exact hD0
    have key := Plasticity.U16.basic_estimate F hmaps hlip hsphere hcover Finset.univ c x
      hcnn hxmem hD' a ha hFa' b hbmem hba
    rw [hsum] at key
    have e1 : ‖b - x 0‖ = g (s - t) := by
      simp only [hx, hg, hb, Matrix.cons_val_zero]
      congr 1; module
    have e2 : ‖b - x 1‖ = g (s + u) := by
      simp only [hx, hg, hb, Matrix.cons_val_one, Matrix.cons_val_zero]
      congr 1; module
    have e3 : ‖b‖ = g s := rfl
    simp only [Fin.sum_univ_two, e1, e2, e3] at key
    simp only [hc, Matrix.cons_val_zero, Matrix.cons_val_one] at key
    linarith
  have hwin := Plasticity.Aux.window_avg_two_point g hglip (1 / 8) t u (‖D‖ / 2)
    (by norm_num) ht0.le hu0.le hK
  have : u * t ^ 2 + t * u ^ 2 = t * u * (t + u) := by ring
  rw [this, show (2 : ℝ) * (1 / 8) = 1 / 4 by norm_num, div_div_eq_mul_div, div_one] at hwin
  nlinarith
