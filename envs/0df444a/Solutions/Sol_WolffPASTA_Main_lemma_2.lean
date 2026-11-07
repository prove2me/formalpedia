-- Prove2me | solution 1 for WolffPASTA.Main.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:08:44.430021+00:00
-- url     : https://prove2.me/submissions/8888b86d-bf2c-46a6-9109-d68eef8739fa

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting
import Theorems.Thm_WolffPASTA_Main_eq_10
import Theorems.Thm_WolffPASTA_Main_eq_11

open MeasureTheory ProbabilityTheory Filter Topology
open WolffPASTA.Main

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAAJoint P A (U N B)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => R (U N B) A lam t ω / t) atTop (𝓝 0) := by
  have hU : ∀ s ω, 0 ≤ s → 0 ≤ U N B s ω ∧ U N B s ω ≤ 1 := by
    intro s ω _
    simp only [U, Set.indicator]
    split_ifs <;> norm_num
  have h11 := eq_11 P A lam hlam hA (U N B) hU hjoint
  have h10 := eq_10 P N A lam hlam hA B hB hpath hjoint hLAA 1 one_pos
  filter_upwards [h10] with ω hω
  set r : ℕ → ℝ := fun n => R (U N B) A lam n ω with hr
  have ha : Tendsto (fun n : ℕ => |r n| / n) atTop (𝓝 0) := by
    have := hω.abs
    simp only [mul_one, abs_zero] at this
    refine this.congr (fun n => ?_)
    rw [abs_div, Nat.abs_cast]
  have ha1 : Tendsto (fun n : ℕ => |r (n + 1)| / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := ha.comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun n => ?_)
    simp [Function.comp]
  have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hbound : Tendsto (fun t : ℝ => |r ⌊t⌋₊| / ⌊t⌋₊ + 2 * (|r (⌊t⌋₊ + 1)| / ((⌊t⌋₊ : ℝ) + 1))
      + lam * t⁻¹) atTop (𝓝 0) := by
    have := ((ha.comp hfl).add ((ha1.comp hfl).const_mul 2)).add
      (tendsto_inv_atTop_zero.const_mul lam)
    simpa using this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  set n := ⌊t⌋₊ with hn
  have ht0 : 0 < t := by linarith
  have hn1 : n ≤ t := Nat.floor_le ht0.le
  have hn2 : t < n + 1 := Nat.lt_floor_add_one t
  have hnpos : (1:ℝ) ≤ n := by
    have : 1 ≤ n := Nat.le_floor (by simpa using ht)
    exact_mod_cast this
  obtain ⟨l1, l2⟩ := h11 ω 1 one_pos n t (by simpa using hn1) (by simpa using hn2.le)
  simp only [mul_one] at l1 l2
  have hr1 : r (n + 1) = R (U N B) A lam ((n:ℝ) + 1) ω := by simp [hr]
  -- |R t| ≤ |r n| + |r (n+1)| + lam
  have habs : |R (U N B) A lam t ω| ≤ |r n| + |r (n + 1)| + lam := by
    rw [abs_le]
    have := abs_nonneg (r n); have := abs_nonneg (r (n+1))
    have := neg_abs_le (r n); have := le_abs_self (r (n + 1))
    rw [hr1] at *
    constructor <;> simp only [hr] at * <;> linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  have e1 : |r n| / n * t ≥ |r n| := by
    rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left hn1 (abs_nonneg _)
  have e2 : 2 * (|r (n + 1)| / ((n : ℝ) + 1)) * t ≥ |r (n + 1)| := by
    rw [mul_div_assoc', div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ (by linarith)]
    have : (n:ℝ) + 1 ≤ 2 * t := by linarith
    nlinarith [abs_nonneg (r (n + 1))]
  have e3 : lam * t⁻¹ * t = lam := by field_simp
  nlinarith
