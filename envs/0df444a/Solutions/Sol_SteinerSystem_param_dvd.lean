-- Prove2me | solution 1 for SteinerSystem.param_dvd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:45:01.965715+00:00
-- url     : https://prove2.me/submissions/00f81fc8-1da2-40c9-baf9-534500fa0a43

import Definitions.Def_SteinerSystem
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset

theorem solution {n k t : ℕ} (ht : 1 ≤ t) (hk : t < k) (S : SteinerSystem n k t) :
    ∀ i < t, (k - i).choose (t - i) ∣ (n - i).choose (t - i) := by
  intro i hi
  by_cases hn : n < t
  · have hni : n - i < t - i := by omega
    rw [Nat.choose_eq_zero_of_lt hni]
    exact Nat.dvd_zero _
  · push Not at hn
    have hin : i ≤ #(Finset.univ : Finset (Fin n)) := by
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨I, _, hI_card⟩ := Finset.exists_subset_card_eq hin
    let B := S.blocks.filter (fun b => I ⊆ b)
    let T := (Finset.univ \ I).powersetCard (t - i)
    have hT_card : #T = (n - i).choose (t - i) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_univ,
          Finset.card_univ, Fintype.card_fin, hI_card]
    have h_eq : T = B.biUnion (fun b => (b \ I).powersetCard (t - i)) := by
      ext c'
      simp only [T, B, Finset.mem_powersetCard, Finset.mem_biUnion, Finset.mem_filter,
        Finset.subset_sdiff, Finset.subset_univ, true_and]
      constructor
      · rintro ⟨hdisj, hc'_card⟩
        have hc_card : #(I ∪ c') = t := by
          rw [Finset.card_union_of_disjoint hdisj.symm, hI_card, hc'_card]
          omega
        obtain ⟨b, ⟨hb_mem, hIb⟩, _⟩ := S.cover (I ∪ c') hc_card
        exact ⟨b, ⟨hb_mem, fun x hx => hIb (Finset.mem_union_left c' hx)⟩,
          ⟨fun x hx => hIb (Finset.mem_union_right I hx), hdisj⟩, hc'_card⟩
      · rintro ⟨b, ⟨_, _⟩, ⟨_, hdisj⟩, hc'_card⟩
        exact ⟨hdisj, hc'_card⟩
    have h_disj : Set.PairwiseDisjoint (B : Set (Finset (Fin n)))
        (fun b => (b \ I).powersetCard (t - i)) := by
      intro b₁ hb₁ b₂ hb₂ hne
      rw [Finset.coe_filter] at hb₁ hb₂
      rw [Function.onFun, Finset.disjoint_left]
      intro c' hc'₁ hc'₂
      rw [Finset.mem_powersetCard, Finset.subset_sdiff] at hc'₁ hc'₂
      have hc_card : #(I ∪ c') = t := by
        rw [Finset.card_union_of_disjoint hc'₁.1.2.symm, hI_card, hc'₁.2]
        omega
      obtain ⟨b, _, hb_uniq⟩ := S.cover (I ∪ c') hc_card
      have h1 : b₁ = b := hb_uniq b₁ ⟨hb₁.1, Finset.union_subset hb₁.2 hc'₁.1.1⟩
      have h2 : b₂ = b := hb_uniq b₂ ⟨hb₂.1, Finset.union_subset hb₂.2 hc'₂.1.1⟩
      exact hne (h1.trans h2.symm)
    rw [← hT_card, h_eq, Finset.card_biUnion h_disj]
    have h_sum : ∑ b ∈ B, #((b \ I).powersetCard (t - i)) =
        ∑ _b ∈ B, (k - i).choose (t - i) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_filter] at hb
      rw [Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hb.2,
          S.sized b hb.1, hI_card]
    rw [h_sum, Finset.sum_const, smul_eq_mul]
    exact dvd_mul_left _ _
