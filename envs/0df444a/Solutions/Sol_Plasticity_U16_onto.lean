-- Prove2me | solution 1 for Plasticity.U16.onto
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:05:04.085731+00:00
-- url     : https://prove2.me/submissions/3013d0e5-7d26-460f-b383-918f2cda100d

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Isometry
import Theorems.Thm_Plasticity_Ext_BishopPhelps

namespace Sol_Plasticity_U16_onto

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

/-- A closed proper subspace is annihilated by a functional of norm one. -/
theorem exists_norm_one_vanishing {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (M : Submodule ℝ Y) (hM : IsClosed (M : Set Y)) (y₀ : Y) (hy₀ : y₀ ∉ M) :
    ∃ φ : StrongDual ℝ Y, ‖φ‖ = 1 ∧ ∀ m ∈ M, φ m = 0 := by
  obtain ⟨f, u, hfu, hM'⟩ := geometric_hahn_banach_point_closed M.convex hM hy₀
  have hu : u < 0 := by simpa using hM' 0 M.zero_mem
  have hvan : ∀ m ∈ M, f m = 0 := by
    intro m hm
    by_contra hne
    have hc := hM' (((u - 1) / f m) • m) (M.smul_mem ((u - 1) / f m) hm)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hc
    linarith
  have hf0 : f ≠ 0 := by
    intro h
    rw [h] at hfu
    simp at hfu
    linarith
  have hfn : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  refine ⟨‖f‖⁻¹ • f, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hfn.ne']
  · intro m hm
    simp [hvan m hm]

end Sol_Plasticity_U16_onto

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1)
    (T : X →ₗᵢ[ℝ] Y) (C : ℝ) (hT : ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x - T x‖ ≤ C * ‖x‖ ^ 2) :
    Function.Surjective T := by
  set M : Submodule ℝ Y := LinearMap.range T.toLinearMap with hM
  have hMset : (M : Set Y) = Set.range T := by
    ext y; simp [hM]
  have hclosed : IsClosed (M : Set Y) := by
    rw [hMset]; exact T.isometry.isClosedEmbedding.isClosed_range
  intro y₀
  by_contra hy
  have hy₀ : y₀ ∉ M := by
    intro h
    rw [← SetLike.mem_coe, hMset] at h
    exact hy h
  obtain ⟨φ, hφ1, hφM⟩ := Sol_Plasticity_U16_onto.exists_norm_one_vanishing M hclosed y₀ hy₀
  obtain ⟨ψ₀, hψ₀φ, y, hy1, hψ₀y⟩ := Plasticity.Ext.BishopPhelps φ (1 / 3) (by norm_num)
  have hψ₀n : |‖ψ₀‖ - 1| < 1 / 3 := by
    have := (abs_norm_sub_norm_le ψ₀ φ).trans_lt hψ₀φ
    rwa [hφ1] at this
  have hψ₀pos : 0 < ‖ψ₀‖ := by
    have := (abs_lt.mp hψ₀n).1
    linarith
  set ψ : StrongDual ℝ Y := ‖ψ₀‖⁻¹ • ψ₀ with hψ
  have hψ1 : ‖ψ‖ = 1 := by
    rw [hψ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hψ₀pos.ne']
  have hψy : ψ y = 1 := by
    rw [hψ, ContinuousLinearMap.smul_apply, hψ₀y, smul_eq_mul, inv_mul_cancel₀ hψ₀pos.ne']
  have hψφ : ‖ψ - φ‖ < 2 / 3 := by
    have h1 : ‖ψ - ψ₀‖ = |1 - ‖ψ₀‖| := by
      have : ψ - ψ₀ = (‖ψ₀‖⁻¹ - 1) • ψ₀ := by rw [hψ]; module
      rw [this, norm_smul, Real.norm_eq_abs]
      rw [show (‖ψ₀‖⁻¹ - 1) = (1 - ‖ψ₀‖) / ‖ψ₀‖ by field_simp]
      rw [abs_div, abs_of_pos hψ₀pos, div_mul_cancel₀ _ hψ₀pos.ne']
    calc ‖ψ - φ‖ = ‖(ψ - ψ₀) + (ψ₀ - φ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖ψ - ψ₀‖ + ‖ψ₀ - φ‖ := norm_add_le _ _
      _ < 1 / 3 + 1 / 3 := by
        rw [h1, abs_sub_comm]
        exact add_lt_add hψ₀n hψ₀φ
      _ = 2 / 3 := by norm_num
  -- y is a unit vector, so y = F a for some a in the ball.
  have hyn : ‖y‖ = 1 := by
    apply le_antisymm hy1
    have := ψ.le_opNorm y
    rw [hψ1, one_mul, hψy] at this
    exact (le_abs_self (1 : ℝ)).trans (by simpa using this)
  obtain ⟨a, ha, hFa⟩ := hcover (by simpa using hyn)
  have ha1 : ‖a‖ ≤ 1 := by simpa using ha
  have hTa := Sol_Plasticity_U16_onto.align F hlip T.toContinuousLinearMap C (fun x hx => hT x hx)
    a ha1 ψ hψ1.le (by rw [hFa, hψy])
  have hφTa : φ (T a) = 0 := hφM _ ⟨a, rfl⟩
  have hbound : (ψ - φ) (T a) ≤ 2 / 3 := by
    calc (ψ - φ) (T a) ≤ ‖(ψ - φ) (T a)‖ := le_abs_self _
      _ ≤ ‖ψ - φ‖ * ‖T a‖ := (ψ - φ).le_opNorm _
      _ ≤ 2 / 3 * 1 := by
        rw [T.norm_map]
        exact mul_le_mul hψφ.le ha1 (norm_nonneg _) (by norm_num)
      _ = 2 / 3 := mul_one _
  rw [ContinuousLinearMap.sub_apply, hφTa, sub_zero] at hbound
  have : ψ (T a) = ψ (T.toContinuousLinearMap a) := rfl
  linarith
