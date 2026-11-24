-- Prove2me | solution 1 for QAOAE3Lin2.General.eq_44_45
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:08:51.31056+00:00
-- url     : https://prove2.me/submissions/e44c1dd6-e0ab-4ce5-8933-284a15c386ae

import Mathlib
import Definitions.Def_QAOAE3Lin2_General_Setting
import Theorems.Thm_QAOAE3Lin2_General_eq_7_odd
import Theorems.Thm_QAOAE3Lin2_General_eq_37
import Theorems.Thm_QAOAE3Lin2_General_eq_41
import Theorems.Thm_QAOAE3Lin2_General_eq_43

open QAOAE3Lin2.General

private lemma gammaGrid_sub (D k r : ℕ) (hk : Odd k) (hr : r ≤ k) :
    gammaGrid D k (k - r) = -gammaGrid D k r := by
  unfold gammaGrid
  have hk_ne : (k : ℝ) ≠ 0 := by
    rcases hk with ⟨t, rfl⟩
    positivity
  have hcast : ((k - r : ℕ) : ℝ) = (k : ℝ) - (r : ℝ) := Nat.cast_sub hr
  have hang : Real.pi * ((k - r : ℕ) : ℝ) / (k : ℝ) = Real.pi - Real.pi * (r : ℝ) / (k : ℝ) := by
    rw [hcast, mul_sub, sub_div, mul_div_cancel_right₀ _ hk_ne]
  rw [hang, Real.cos_pi_sub, neg_div]

private lemma rem_bound (D k r : ℕ) (hD : 1 ≤ D) :
    (9 * Real.sqrt D * |gammaGrid D k r|) ^ (k + 2) ≤ (9 / 10 : ℝ) ^ (k + 2) := by
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
  have hsqrt_ne : Real.sqrt D ≠ 0 := ne_of_gt hsqrt_pos
  have hbase_nonneg : 0 ≤ 9 * Real.sqrt D * |gammaGrid D k r| := by positivity
  have hbase_le : 9 * Real.sqrt D * |gammaGrid D k r| ≤ 9 / 10 := by
    unfold gammaGrid
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 10 * Real.sqrt D)]
    have hcalc : 9 * Real.sqrt D * (|Real.cos (Real.pi * ↑r / ↑k)| / (10 * Real.sqrt D)) =
        (9 / 10 : ℝ) * |Real.cos (Real.pi * ↑r / ↑k)| := by
      calc 9 * Real.sqrt D * (|Real.cos (Real.pi * ↑r / ↑k)| / (10 * Real.sqrt D))
          = (9 / 10 : ℝ) * |Real.cos (Real.pi * ↑r / ↑k)| * (Real.sqrt D / Real.sqrt D) := by ring
        _ = (9 / 10 : ℝ) * |Real.cos (Real.pi * ↑r / ↑k)| * 1 := by rw [div_self hsqrt_ne]
        _ = (9 / 10 : ℝ) * |Real.cos (Real.pi * ↑r / ↑k)| := by ring
    rw [hcalc]
    have hcos : |Real.cos (Real.pi * ↑r / ↑k)| ≤ 1 := Real.abs_cos_le_one _
    linarith
  gcongr

theorem solution :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∃ k : ℕ, Odd k ∧ 5 * Real.log D ≤ k ∧
      (k : ℝ) ≤ 5 * Real.log D + 2 ∧
      ∀ (n m : ℕ) (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool),
        IsTripleFamily tri → BoundedOccurrence tri D →
        ∃ r ∈ Finset.range (k + 1),
          (1 / 2 + 1 / (101 * Real.sqrt D * Real.log D)) * (m : ℝ) ≤
            expSat tri rhs (gammaGrid D k r) (Real.pi / 4) := by
  obtain ⟨D₀', h43_all⟩ := eq_43
  refine ⟨max D₀' 1, fun D hD_max => ?_⟩
  have hD₀' : D₀' ≤ D := le_of_max_le_left hD_max
  have hD : 1 ≤ D := le_of_max_le_right hD_max
  obtain ⟨k, hk, hk_lo, hk_hi, h43⟩ := h43_all D hD₀'
  refine ⟨k, hk, hk_lo, hk_hi, fun n m tri rhs htri hocc => ?_⟩
  obtain ⟨r₀, hr₀_mem, h41⟩ := eq_41 tri rhs D hD k hk
  have hr₀_le : r₀ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr₀_mem)
  have h37 := eq_37 tri rhs D htri hocc hD k hk (gammaGrid D k r₀)
  have hrem : (m : ℝ) * (9 * Real.sqrt D * |gammaGrid D k r₀|) ^ (k + 2) ≤
      (m : ℝ) * (9 / 10 : ℝ) ^ (k + 2) :=
    mul_le_mul_of_nonneg_left (rem_bound D k r₀ hD) (Nat.cast_nonneg m)
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h43_m : (1 / (101 * Real.sqrt D * Real.log D)) * (m : ℝ) ≤
      (1 / (20 * Real.sqrt D * k) - (9 / 10 : ℝ) ^ (k + 2)) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt h43) hm_nonneg
  have h42_lhs : (1 / (20 * Real.sqrt D * k) - (9 / 10 : ℝ) ^ (k + 2)) * (m : ℝ) =
      (m : ℝ) / (20 * Real.sqrt D * k) - (m : ℝ) * (9 / 10 : ℝ) ^ (k + 2) := by ring
  have habs_bound : (1 / (101 * Real.sqrt D * Real.log D)) * (m : ℝ) ≤
      |expSat tri rhs (-gammaGrid D k r₀) (Real.pi / 4) - (m : ℝ) / 2| := by
    linarith
  rcases le_or_gt 0 (expSat tri rhs (-gammaGrid D k r₀) (Real.pi / 4) - (m : ℝ) / 2) with hpos | hneg
  · refine ⟨k - r₀, Finset.mem_range.mpr (by omega), ?_⟩
    have hsub := gammaGrid_sub D k r₀ hk hr₀_le
    rw [hsub]
    rw [abs_of_nonneg hpos] at habs_bound
    linarith
  · refine ⟨r₀, hr₀_mem, ?_⟩
    have hodd := eq_7_odd tri rhs (gammaGrid D k r₀) (Real.pi / 4)
    rw [abs_of_neg hneg] at habs_bound
    linarith
