-- Prove2me | solution 1 for RovelliLQG.areaSpectrum_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:39:53.616087+00:00
-- url     : https://prove2.me/submissions/a6c67e0a-3e4d-48f7-8dc6-e4144cd5900a

import Mathlib
import Definitions.Def_RovelliLQG_Defs

set_option autoImplicit false

open scoped InnerProductSpace

open RovelliLQG in
lemma p88_half_le (k : ℕ) : (k : ℝ) / 2 ≤ casimirRoot ((k : ℝ) / 2) := by
  unfold casimirRoot
  have h0 : (0:ℝ) ≤ (k:ℝ) / 2 := by positivity
  calc (k:ℝ) / 2 = Real.sqrt (((k:ℝ) / 2) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((k:ℝ) / 2 * ((k:ℝ) / 2 + 1)) := Real.sqrt_le_sqrt (by nlinarith)

open RovelliLQG in
lemma p88_filter (ks : Multiset ℕ) :
    (ks.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum
      = ((ks.filter (· ≠ 0)).map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum := by
  conv_lhs => rw [← Multiset.filter_add_not (· ≠ 0) ks]
  rw [Multiset.map_add, Multiset.sum_add]
  have hz : ((ks.filter (fun k => ¬ (k ≠ 0))).map
      (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Multiset.mem_filter] at hk
    have hk0 : k = 0 := by simpa using hk.2
    subst hk0
    simp [casimirRoot]
  rw [hz, add_zero]

open RovelliLQG in
lemma p88_bound (ks : Multiset ℕ) :
    (ks.sum : ℝ) ≤ 2 * (ks.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum := by
  rw [Nat.cast_multiset_sum, ← Multiset.sum_map_mul_left]
  apply Multiset.sum_map_le_sum_map
  intro k _
  have := p88_half_le k
  linarith

lemma p88_le (N : ℕ) (m : Multiset ℕ) (hpos : ∀ k ∈ m, k ≠ 0) (hs : m.sum ≤ N) :
    m ≤ N • Multiset.range (N + 1) := by
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a ∈ m
  · have hle : a ≤ N := le_trans (Multiset.le_sum_of_mem ha) hs
    have hcard : Multiset.card m ≤ N := by
      have h1 : Multiset.card m • (1 : ℕ) ≤ m.sum :=
        Multiset.card_nsmul_le_sum (fun x hx => Nat.one_le_iff_ne_zero.mpr (hpos x hx))
      simp only [smul_eq_mul, mul_one] at h1
      omega
    rw [Multiset.count_nsmul,
      Multiset.count_eq_one_of_mem (Multiset.nodup_range (N + 1)) (Multiset.mem_range.mpr (by omega))]
    simpa using le_trans (Multiset.count_le_card a m) hcard
  · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _

open RovelliLQG in
theorem solution (γ ħ G : ℝ) (hγ : 0 < γ) (hħ : 0 < ħ) (hG : 0 < G)
    (R : ℝ) : {A ∈ areaSpectrum γ ħ G | A ≤ R}.Finite := by
  have hcpos : 0 < 8 * Real.pi * γ * ħ * G := by positivity
  set c := 8 * Real.pi * γ * ħ * G with hc
  set N : ℕ := ⌈2 * R / c⌉₊ with hN
  let f : Multiset ℕ → ℝ := fun m => c * (m.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum
  apply Set.Finite.subset
    (Set.Finite.image f ((N • Multiset.range (N + 1)).powerset.toFinset.finite_toSet))
  rintro A ⟨⟨ks, hA⟩, hR⟩
  set m := ks.filter (· ≠ 0) with hm
  have hval : A = f m := by
    simp only [f]
    rw [hA, p88_filter]
  have hpos : ∀ k ∈ m, k ≠ 0 := fun k hk => (Multiset.mem_filter.mp hk).2
  have hS : (m.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum ≤ R / c := by
    rw [le_div_iff₀ hcpos]
    have : A = c * (m.map (fun k : ℕ => casimirRoot ((k : ℝ) / 2))).sum := hval
    linarith
  have hsumR : (m.sum : ℝ) ≤ N := by
    have h1 := p88_bound m
    have h2 : 2 * R / c ≤ (N : ℝ) := Nat.le_ceil _
    have h3 : 2 * (R / c) = 2 * R / c := by ring
    linarith
  have hsum : m.sum ≤ N := by exact_mod_cast hsumR
  refine ⟨m, ?_, hval.symm⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset]
  exact p88_le N m hpos hsum
