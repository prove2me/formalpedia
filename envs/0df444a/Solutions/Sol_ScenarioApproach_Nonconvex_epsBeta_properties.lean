-- Prove2me | solution 1 for ScenarioApproach.Nonconvex.epsBeta_properties
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:12:05.315223+00:00
-- url     : https://prove2.me/submissions/0a04181a-1cf6-4bd7-9c43-f0b4e3eed3c9

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_epsBeta

open ScenarioApproach.Nonconvex in
lemma epsBeta_aux_pow (N : ℕ) (β : ℝ) (hβ0 : 0 ≤ β) (k : ℕ) (hk : k < N) :
    (1 - epsBeta N β k) ^ (N - k) = β / ((N : ℝ) * (N.choose k : ℝ)) := by
  have hne : k ≠ N := Nat.ne_of_lt hk
  unfold epsBeta
  rw [if_neg hne, sub_sub_cancel]
  have hm : (0 : ℝ) < ((N - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hx : 0 ≤ β / ((N : ℝ) * (N.choose k : ℝ)) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel hm.ne', Real.rpow_one]

open ScenarioApproach.Nonconvex in
lemma epsBeta_aux_mem (N : ℕ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (k : ℕ) (hk : k ≤ N) :
    epsBeta N β k ∈ Set.Icc (0 : ℝ) 1 := by
  unfold epsBeta
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · have hk' : k < N := lt_of_le_of_ne hk h
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have hC1 : (1 : ℝ) ≤ (N.choose k : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.choose_pos hk).ne'
    have hD : (1 : ℝ) ≤ (N : ℝ) * (N.choose k : ℝ) := by nlinarith
    have hx0 : 0 ≤ β / ((N : ℝ) * (N.choose k : ℝ)) := by positivity
    have hx1 : β / ((N : ℝ) * (N.choose k : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hm : (0 : ℝ) ≤ (1 : ℝ) / ((N - k : ℕ) : ℝ) := by positivity
    have h0 := Real.rpow_nonneg hx0 ((1 : ℝ) / ((N - k : ℕ) : ℝ))
    have h1 := Real.rpow_le_one hx0 hx1 hm
    constructor <;> linarith

open ScenarioApproach.Nonconvex in
theorem solution (N : ℕ) (hN : 1 ≤ N) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∀ k ≤ N, epsBeta N β k ∈ Set.Icc (0 : ℝ) 1) ∧ epsBeta N β N = 1 ∧
      ∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - epsBeta N β k) ^ (N - k) = β := by
  refine ⟨fun k hk => epsBeta_aux_mem N β hβ0 hβ1 k hk, ?_, ?_⟩
  · unfold epsBeta; simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have : ∀ k ∈ Finset.range N,
        (N.choose k : ℝ) * (1 - epsBeta N β k) ^ (N - k) = β / N := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [epsBeta_aux_pow N β hβ0 k hk']
      have hC : (0 : ℝ) < (N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk'.le
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
