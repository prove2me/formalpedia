-- Prove2me | solution 1 for Plasticity.U16.complete
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:02:58.450072+00:00
-- url     : https://prove2.me/submissions/1f89290a-bd16-4bec-bc35-3dba1ef36378

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_A01

namespace Sol_Plasticity_U16_complete

/-- A functional of norm at most one that norms `F a` also takes a value at least one at `T a`,
when `T` is linear and `‖F x - T x‖ ≤ C ‖x‖²` on the ball. -/
theorem align {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y) (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (T : X →L[ℝ] Y) (C : ℝ)
    (hT : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ C * ‖x‖ ^ 2)
    (a : X) (ha : ‖a‖ ≤ 1) (ψ : StrongDual ℝ Y) (hψ : ‖ψ‖ ≤ 1) (hψa : ψ (F a) = 1) :
    1 ≤ ψ (T a) := by
  have hball : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • a ∈ Metric.closedBall (0 : X) 1 := by
    intro t ht0 ht1
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht0]
    nlinarith [norm_nonneg a]
  have hkey : ∀ t : ℝ, 0 < t → t ≤ 1 → t - |C| * t ^ 2 ≤ t * ψ (T a) := by
    intro t ht0 ht1
    have hta := hball t ht0.le ht1
    have ha' : a ∈ Metric.closedBall (0 : X) 1 := by simpa using ha
    -- ψ (F (t a)) ≥ t
    have h1 : t ≤ ψ (F (t • a)) := by
      have hd : ‖F a - F (t • a)‖ ≤ 1 - t := by
        have := hlip.norm_sub_le ha' hta
        have hn : ‖a - t • a‖ = (1 - t) * ‖a‖ := by
          rw [show a - t • a = (1 - t) • a by module, norm_smul, Real.norm_of_nonneg (by linarith)]
        rw [hn] at this
        simp only [NNReal.coe_one, one_mul] at this
        nlinarith [norm_nonneg a]
      have hψd : ψ (F a) - ψ (F (t • a)) ≤ 1 - t := by
        rw [← map_sub]
        calc ψ (F a - F (t • a)) ≤ ‖ψ (F a - F (t • a))‖ := le_abs_self _
          _ ≤ ‖ψ‖ * ‖F a - F (t • a)‖ := ψ.le_opNorm _
          _ ≤ 1 * (1 - t) := by gcongr
          _ = 1 - t := one_mul _
      linarith
    -- |ψ (F (t a)) - t ψ (T a)| ≤ |C| t²
    have h2 : ψ (F (t • a)) - t * ψ (T a) ≤ |C| * t ^ 2 := by
      have hb := hT (t • a) hta
      have hn : ‖t • a‖ ^ 2 ≤ t ^ 2 := by
        rw [norm_smul, Real.norm_of_nonneg ht0.le, mul_pow]
        have : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
        nlinarith [sq_nonneg t]
      have hC : C * ‖t • a‖ ^ 2 ≤ |C| * t ^ 2 := by
        calc C * ‖t • a‖ ^ 2 ≤ |C| * ‖t • a‖ ^ 2 := by gcongr; exact le_abs_self C
          _ ≤ |C| * t ^ 2 := by gcongr
      have : ψ (F (t • a)) - t * ψ (T a) = ψ (F (t • a) - T (t • a)) := by
        rw [map_sub, map_smul, map_smul, smul_eq_mul]
      rw [this]
      calc ψ (F (t • a) - T (t • a)) ≤ ‖ψ (F (t • a) - T (t • a))‖ := le_abs_self _
        _ ≤ ‖ψ‖ * ‖F (t • a) - T (t • a)‖ := ψ.le_opNorm _
        _ ≤ 1 * (C * ‖t • a‖ ^ 2) := by gcongr
        _ ≤ |C| * t ^ 2 := by linarith
    linarith
  by_contra hlt
  push Not at hlt
  set δ := 1 - ψ (T a) with hδ
  have hδ0 : 0 < δ := by linarith
  set t : ℝ := min 1 (δ / (2 * (|C| + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ δ / (2 * (|C| + 1)) := min_le_right _ _
  have h := hkey t ht0 ht1
  -- divide by t: 1 - |C| t ≤ ψ (T a)
  have h' : 1 - |C| * t ≤ ψ (T a) := by
    have : t * (1 - |C| * t) ≤ t * ψ (T a) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hCt : |C| * t ≤ δ / 2 := by
    have hpos : 0 < 2 * (|C| + 1) := by positivity
    have : t * (2 * (|C| + 1)) ≤ δ := by
      rwa [le_div_iff₀ hpos] at ht2
    nlinarith [abs_nonneg C]
  linarith

end Sol_Plasticity_U16_complete

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (T : X ≃ₗᵢ[ℝ] Y) (C : ℝ) (hT : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ C * ‖x‖ ^ 2) :
    Set.EqOn F T (Metric.closedBall (0 : X) 1) := by
  set H : X → X := fun x => T.symm (F x) with hH
  have hHmaps : Set.MapsTo H (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1) := by
    intro x hx
    have := hmaps hx
    simpa [hH, mem_closedBall_zero_iff] using this
  have hHlip : LipschitzOnWith 1 H (Metric.closedBall (0 : X) 1) := by
    have h1 : LipschitzWith 1 T.symm := T.symm.isometry.lipschitz
    have h2 := h1.comp_lipschitzOnWith hlip
    rw [mul_one] at h2
    exact h2
  have hHalign : ∀ a ∈ Metric.sphere (0 : X) 1, ‖a + H a‖ = 2 := by
    intro a ha
    have ha1 : ‖a‖ = 1 := by simpa using ha
    have hFa : ‖F a‖ = 1 := by simpa using hsphere ha
    obtain ⟨ψ, hψ1, hψa⟩ := exists_dual_vector ℝ (F a) (by rw [hFa]; norm_num)
    rw [hFa] at hψa
    replace hψa : ψ (F a) = 1 := by simpa using hψa
    have hTa := Sol_Plasticity_U16_complete.align F hlip
      (T.toLinearIsometry.toContinuousLinearMap) C (fun x hx => hT x hx) a ha1.le ψ hψ1.le hψa
    have hle : ‖a + H a‖ ≤ 2 := by
      have hHa : ‖H a‖ ≤ 1 := by
        simpa using hHmaps (Metric.sphere_subset_closedBall ha)
      calc ‖a + H a‖ ≤ ‖a‖ + ‖H a‖ := norm_add_le _ _
        _ ≤ 2 := by linarith
    have hge : 2 ≤ ‖a + H a‖ := by
      have heq : ‖a + H a‖ = ‖T a + F a‖ := by
        rw [← T.norm_map (a + H a), map_add]
        simp [hH]
      rw [heq]
      have : ψ (T a + F a) ≤ ‖T a + F a‖ := by
        calc ψ (T a + F a) ≤ ‖ψ (T a + F a)‖ := le_abs_self _
          _ ≤ ‖ψ‖ * ‖T a + F a‖ := ψ.le_opNorm _
          _ = ‖T a + F a‖ := by rw [hψ1, one_mul]
      rw [map_add, hψa] at this
      have : ψ (T a) = ψ ((T.toLinearIsometry.toContinuousLinearMap) a) := rfl
      linarith
    linarith
  have hid := Plasticity.A01 H hHmaps hHlip hHalign
  intro x hx
  have h := hid hx
  simp only [hH, id] at h
  calc F x = T (T.symm (F x)) := (T.apply_symm_apply _).symm
    _ = T x := by rw [h]
