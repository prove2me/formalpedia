-- Prove2me | solution 1 for StrictCompatLB.Inhomogeneous.subcritical_of_A19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:53:12.543355+00:00
-- url     : https://prove2.me/submissions/ef31f781-04c8-4b8b-a2f3-b515d8e354dd

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

open Finset Filter

/-- number of `k`-subsets (`k ≥ 1`) of `S` containing `v`. -/
lemma inhomA19_count {α : Type*} [DecidableEq α] (S : Finset α) (v : α) (j : ℕ) :
    ((S.powersetCard (j + 1)).filter (fun U => v ∈ U)).card =
      if v ∈ S then Nat.choose (S.card - 1) j else 0 := by
  split_ifs with hv
  · have hS : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
    have hnv : v ∉ S.erase v := Finset.notMem_erase v S
    rw [hS, Finset.powersetCard_succ_insert hnv, Finset.filter_union]
    have h1 : ((S.erase v).powersetCard (j + 1)).filter (fun U => v ∈ U) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro U hU hvU
      exact hnv ((Finset.mem_powersetCard.mp hU).1 hvU)
    have h2 : (((S.erase v).powersetCard j).image (insert v)).filter (fun U => v ∈ U) =
        ((S.erase v).powersetCard j).image (insert v) := by
      apply Finset.filter_true_of_mem
      intro U hU
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hU
      exact Finset.mem_insert_self v T
    rw [h1, h2, Finset.empty_union, Finset.card_image_of_injOn, Finset.card_powersetCard,
      Finset.card_erase_of_mem hv]
    · rw [← hS]
    · intro A hA B hB hAB
      have hA' : v ∉ A := fun h => hnv ((Finset.mem_powersetCard.mp hA).1 h)
      have hB' : v ∉ B := fun h => hnv ((Finset.mem_powersetCard.mp hB).1 h)
      rw [← Finset.erase_insert hA', hAB, Finset.erase_insert hB']
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro U hU hvU
    exact hv ((Finset.mem_powersetCard.mp hU).1 hvU)

lemma inhomA19_term {α : Type*} [DecidableEq α] (S : Finset α) (v : α) (d : ℕ) (hd : 1 ≤ d) :
    ((Nat.choose S.card (min d S.card) : ℕ) : ℝ)⁻¹ *
        ∑ U ∈ S.powersetCard (min d S.card), (if v ∈ U then ((U.card : ℕ) : ℝ)⁻¹ else 0)
      = if v ∈ S then ((S.card : ℕ) : ℝ)⁻¹ else 0 := by
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    have hn : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    have hk1 : 1 ≤ min d S.card := le_min hd hn
    obtain ⟨j, hj⟩ : ∃ j, min d S.card = j + 1 := ⟨min d S.card - 1, by omega⟩
    have hsum : ∑ U ∈ S.powersetCard (min d S.card), (if v ∈ U then ((U.card : ℕ) : ℝ)⁻¹ else 0)
        = ((Nat.choose m j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)⁻¹ := by
      have : ∀ U ∈ S.powersetCard (min d S.card),
          (if v ∈ U then ((U.card : ℕ) : ℝ)⁻¹ else 0) =
            (if v ∈ U then ((j + 1 : ℕ) : ℝ)⁻¹ else 0) := by
        intro U hU
        rw [(Finset.mem_powersetCard.mp hU).2, hj]
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hj,
        inhomA19_count, if_pos hv, hm]
      simp
    rw [hsum, hj, hm]
    have key : ((m + 1 : ℕ) : ℝ) * (Nat.choose m j : ℝ) =
        (Nat.choose (m + 1) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    have hc : (0 : ℝ) < (Nat.choose (m + 1) (j + 1) : ℝ) := by
      have : j + 1 ≤ m + 1 := by rw [← hj, ← hm]; exact min_le_right _ _
      exact_mod_cast Nat.choose_pos this
    have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hj0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    field_simp
    linarith [key]
  · rw [if_neg hv]
    have : ∀ U ∈ S.powersetCard (min d S.card),
        (if v ∈ U then ((U.card : ℕ) : ℝ)⁻¹ else 0) = 0 := by
      intro U hU
      rw [if_neg]
      intro hvU
      exact hv ((Finset.mem_powersetCard.mp hU).1 hvU)
    rw [Finset.sum_congr rfl this]
    simp

theorem solution (d : ℕ) (hd : 1 ≤ d) (M : ℕ → ℕ)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (h : StrictCompatLB.RegularDegree.SatisfiesA19 M G) :
    StrictCompatLB.MeanField.IsSubcritical d M G := by
  classical
  refine ⟨fun N w U v => if v ∈ U then ((U.card : ℕ) : ℝ)⁻¹ else 0, ?_, ?_, ?_, ?_⟩
  · intro N w U v
    dsimp only
    split_ifs <;> positivity
  · intro N w U v hv
    simp [hv]
  · intro N w U hU
    rw [← Finset.sum_filter, Finset.filter_true_of_mem (fun x hx => hx), Finset.sum_const,
      nsmul_eq_mul]
    have : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
    field_simp
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨N₀, fun N hN v => ?_⟩
    have := hN₀ N hN v
    convert this using 3 with w _
    dsimp only
    rw [inhomA19_term _ v d hd]
    congr 1
    simp [StrictCompatLB.MeanField.nbrW]
