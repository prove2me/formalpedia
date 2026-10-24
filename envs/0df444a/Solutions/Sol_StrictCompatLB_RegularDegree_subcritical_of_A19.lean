-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.subcritical_of_A19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:53:37.467559+00:00
-- url     : https://prove2.me/submissions/85b81ee6-10c1-4923-aedf-8a9ecdbaac79

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

open Finset Filter

namespace StrictCompatLB.RegularDegree

lemma term_eq (d : ℕ) (hd : 2 ≤ d) {N : ℕ} (S : Finset (Fin N)) (v : Fin N) :
    ((Nat.choose S.card (min d S.card) : ℕ) : ℝ)⁻¹ *
      ∑ U ∈ S.powersetCard (min d S.card), (if v ∈ U then ((U.card : ℝ))⁻¹ else 0)
    = if v ∈ S then (S.card : ℝ)⁻¹ else 0 := by
  classical
  set k := min d S.card with hk
  have hsum : ∑ U ∈ S.powersetCard k, (if v ∈ U then ((U.card : ℝ))⁻¹ else 0)
      = ∑ U ∈ (S.powersetCard k).filter (fun U => {v} ⊆ U), ((k : ℝ))⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.mem_powersetCard] at hU
    simp [hU.2]
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  split_ifs with hv
  · have hn : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
    have hk1 : 1 ≤ k := by rw [hk]; omega
    rw [Finset.card_filter_powersetCard_subset {v} S k (by simpa using hv) (by simpa using hk1)]
    simp only [Finset.card_singleton]
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hm, hj]
    simp only [Nat.add_sub_cancel]
    have key := Nat.add_one_mul_choose_eq m j
    have key' : ((m + 1 : ℕ) : ℝ) * (m.choose j : ℝ) = ((m+1).choose (j+1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast key
    have hc : ((m+1).choose (j+1) : ℝ) ≠ 0 := by
      have : j + 1 ≤ m + 1 := by omega
      exact_mod_cast (Nat.choose_pos this).ne'
    field_simp
    push_cast at key' ⊢
    linarith
  · have : (S.powersetCard k).filter (fun U => {v} ⊆ U) = ∅ := by
      apply Finset.filter_false_of_mem
      intro U hU hvU
      rw [Finset.mem_powersetCard] at hU
      exact hv (hU.1 (by simpa using hvU))
    rw [this]; simp

theorem subcritical_of_A19' (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (hG : SatisfiesA19 M G) :
    StrictCompatLB.MeanField.IsSubcritical d M G := by
  classical
  refine ⟨fun N w U v => if v ∈ U then ((U.card : ℝ))⁻¹ else 0, ?_, ?_, ?_, ?_⟩
  · intro N w U v; dsimp only; split_ifs <;> positivity
  · intro N w U v hv; simp [hv]
  · intro N w U hU
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_self, Finset.sum_const,
      nsmul_eq_mul]
    have : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.card_pos.ne'
    field_simp
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := hG ε hε
    refine ⟨N₀, fun N hN v => ?_⟩
    have := hN₀ N hN v
    convert this using 3
    dsimp only
    rw [term_eq d hd]
    simp [StrictCompatLB.MeanField.nbrW]

end StrictCompatLB.RegularDegree

theorem solution (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (hG : StrictCompatLB.RegularDegree.SatisfiesA19 M G) :
    StrictCompatLB.MeanField.IsSubcritical d M G :=
  StrictCompatLB.RegularDegree.subcritical_of_A19' d hd M G hG
