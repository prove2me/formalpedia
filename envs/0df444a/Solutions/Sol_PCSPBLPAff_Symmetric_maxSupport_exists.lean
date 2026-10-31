-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.maxSupport_exists
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:50:53.949531+00:00
-- url     : https://prove2.me/submissions/95f717a3-472a-4f11-ac3f-8687731e211a

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

set_option autoImplicit false

namespace PCSPBLPAff.Symmetric

section MaxSupportProof

variable {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]

def wMid {X : Instance τ ar} (w₁ w₂ : Fin X.n → A → ℚ) (i : Fin X.n) (a : A) : ℚ :=
  (w₁ i a + w₂ i a) / 2

def pMid {X : Instance τ ar} (p₁ p₂ : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ)
    (j : Fin X.m) (y : Fin (ar (X.sym j)) → A) : ℚ :=
  (p₁ j y + p₂ j y) / 2

theorem isLPSol_mid {X : Instance τ ar} {𝔸 : RelStruct τ ar A}
    {w₁ w₂ : Fin X.n → A → ℚ}
    {p₁ p₂ : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ}
    (h₁ : IsLPSol X 𝔸 w₁ p₁) (h₂ : IsLPSol X 𝔸 w₂ p₂) :
    IsLPSol X 𝔸 (wMid w₁ w₂) (pMid p₁ p₂) := by
  rcases h₁ with ⟨hw₁, hp₁, hrel₁, hsumw₁, hsump₁, hmarg₁⟩
  rcases h₂ with ⟨hw₂, hp₂, hrel₂, hsumw₂, hsump₂, hmarg₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i a
    unfold wMid
    linarith [hw₁ i a, hw₂ i a]
  · intro j y
    unfold pMid
    linarith [hp₁ j y, hp₂ j y]
  · intro j y hy
    unfold pMid
    rw [hrel₁ j y hy, hrel₂ j y hy]
    ring
  · intro i
    unfold wMid
    simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, hsumw₁ i, hsumw₂ i]
    norm_num
  · intro j
    unfold pMid
    simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, hsump₁ j, hsump₂ j]
    norm_num
  · intro j k a
    unfold pMid wMid
    simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, hmarg₁ j k a, hmarg₂ j k a]

theorem add_div_two_ne_zero_left {x y : ℚ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≠ 0) :
    (x + y) / 2 ≠ 0 := by
  have hxpos : 0 < x := lt_of_le_of_ne hx0 hx.symm
  intro h
  linarith

theorem add_div_two_ne_zero_right {x y : ℚ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≠ 0) :
    (x + y) / 2 ≠ 0 := by
  have hypos : 0 < y := lt_of_le_of_ne hy0 hy.symm
  intro h
  linarith

noncomputable def WSet {X : Instance τ ar} (w : Fin X.n → A → ℚ) : Finset (Fin X.n × A) :=
  Finset.univ.filter (fun ia => w ia.1 ia.2 ≠ 0)

noncomputable def PSet {X : Instance τ ar}
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) :
    Finset ((j : Fin X.m) × (Fin (ar (X.sym j)) → A)) :=
  Finset.univ.filter (fun jy => p jy.1 jy.2 ≠ 0)

theorem WSet_sub_left {X : Instance τ ar} {𝔸 : RelStruct τ ar A}
    {w₁ w₂ : Fin X.n → A → ℚ}
    {p₁ p₂ : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ}
    (h₁ : IsLPSol X 𝔸 w₁ p₁) (h₂ : IsLPSol X 𝔸 w₂ p₂) :
    WSet w₁ ⊆ WSet (wMid w₁ w₂) := by
  intro ia hia
  simp only [WSet, Finset.mem_filter, Finset.mem_univ, true_and] at hia ⊢
  exact add_div_two_ne_zero_left (h₁.1 ia.1 ia.2) (h₂.1 ia.1 ia.2) hia

theorem PSet_sub_left {X : Instance τ ar} {𝔸 : RelStruct τ ar A}
    {w₁ w₂ : Fin X.n → A → ℚ}
    {p₁ p₂ : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ}
    (h₁ : IsLPSol X 𝔸 w₁ p₁) (h₂ : IsLPSol X 𝔸 w₂ p₂) :
    PSet p₁ ⊆ PSet (pMid p₁ p₂) := by
  intro jy hjy
  simp only [PSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjy ⊢
  exact add_div_two_ne_zero_left (h₁.2.1 jy.1 jy.2) (h₂.2.1 jy.1 jy.2) hjy

theorem maxSupport_aux (X : Instance τ ar) (𝔸 : RelStruct τ ar A) :
    ∀ (k : ℕ) (w : Fin X.n → A → ℚ) (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ),
      IsLPSol X 𝔸 w p →
      (Fintype.card (Fin X.n × A) - (WSet w).card) +
        (Fintype.card ((j : Fin X.m) × (Fin (ar (X.sym j)) → A)) - (PSet p).card) ≤ k →
      ∃ w' p', IsMaxSupportLPSol X 𝔸 w' p' := by
  intro k
  induction k with
  | zero =>
    intro w p hlp hle
    by_cases hmax : IsMaxSupportLPSol X 𝔸 w p
    · exact ⟨w, p, hmax⟩
    · unfold IsMaxSupportLPSol at hmax
      push_neg at hmax
      obtain ⟨w₂, p₂, hlp₂, hnot⟩ := hmax hlp
      have hw_le : (WSet (wMid w w₂)).card ≤ Fintype.card (Fin X.n × A) := Finset.card_le_univ _
      have hp_le : (PSet (pMid p p₂)).card ≤
          Fintype.card ((j : Fin X.m) × (Fin (ar (X.sym j)) → A)) := Finset.card_le_univ _
      have hw_sub : (WSet w).card ≤ (WSet (wMid w w₂)).card :=
        Finset.card_le_card (WSet_sub_left hlp hlp₂)
      have hp_sub : (PSet p).card ≤ (PSet (pMid p p₂)).card :=
        Finset.card_le_card (PSet_sub_left hlp hlp₂)
      by_cases hw_all : ∀ i a, w₂ i a ≠ 0 → w i a ≠ 0
      · obtain ⟨j, y, hjy₂, hjy₁⟩ := hnot hw_all
        have hlt : (PSet p).card < (PSet (pMid p p₂)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (PSet_sub_left hlp hlp₂)]
          refine ⟨⟨j, y⟩, ?_, ?_⟩
          · simp only [PSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact add_div_two_ne_zero_right (hlp.2.1 j y) (hlp₂.2.1 j y) hjy₂
          · simp [PSet, hjy₁]
        omega
      · push_neg at hw_all
        obtain ⟨i, a, hia₂, hia₁⟩ := hw_all
        have hlt : (WSet w).card < (WSet (wMid w w₂)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (WSet_sub_left hlp hlp₂)]
          refine ⟨(i, a), ?_, ?_⟩
          · simp only [WSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact add_div_two_ne_zero_right (hlp.1 i a) (hlp₂.1 i a) hia₂
          · simp [WSet, hia₁]
        omega
  | succ k ih =>
    intro w p hlp hle
    by_cases hmax : IsMaxSupportLPSol X 𝔸 w p
    · exact ⟨w, p, hmax⟩
    · unfold IsMaxSupportLPSol at hmax
      push_neg at hmax
      obtain ⟨w₂, p₂, hlp₂, hnot⟩ := hmax hlp
      have hw_le : (WSet (wMid w w₂)).card ≤ Fintype.card (Fin X.n × A) := Finset.card_le_univ _
      have hp_le : (PSet (pMid p p₂)).card ≤
          Fintype.card ((j : Fin X.m) × (Fin (ar (X.sym j)) → A)) := Finset.card_le_univ _
      have hw_sub : (WSet w).card ≤ (WSet (wMid w w₂)).card :=
        Finset.card_le_card (WSet_sub_left hlp hlp₂)
      have hp_sub : (PSet p).card ≤ (PSet (pMid p p₂)).card :=
        Finset.card_le_card (PSet_sub_left hlp hlp₂)
      apply ih (wMid w w₂) (pMid p p₂) (isLPSol_mid hlp hlp₂)
      by_cases hw_all : ∀ i a, w₂ i a ≠ 0 → w i a ≠ 0
      · obtain ⟨j, y, hjy₂, hjy₁⟩ := hnot hw_all
        have hlt : (PSet p).card < (PSet (pMid p p₂)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (PSet_sub_left hlp hlp₂)]
          refine ⟨⟨j, y⟩, ?_, ?_⟩
          · simp only [PSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact add_div_two_ne_zero_right (hlp.2.1 j y) (hlp₂.2.1 j y) hjy₂
          · simp [PSet, hjy₁]
        omega
      · push_neg at hw_all
        obtain ⟨i, a, hia₂, hia₁⟩ := hw_all
        have hlt : (WSet w).card < (WSet (wMid w w₂)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (WSet_sub_left hlp hlp₂)]
          refine ⟨(i, a), ?_, ?_⟩
          · simp only [WSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact add_div_two_ne_zero_right (hlp.1 i a) (hlp₂.1 i a) hia₂
          · simp [WSet, hia₁]
        omega

end MaxSupportProof

end PCSPBLPAff.Symmetric

open PCSPBLPAff.Symmetric in
theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (h : IsLPSol X 𝔸 w p) :
    ∃ (w' : Fin X.n → A → ℚ) (p' : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ),
      IsMaxSupportLPSol X 𝔸 w' p' :=
  maxSupport_aux X 𝔸
    ((Fintype.card (Fin X.n × A) - (WSet w).card) +
      (Fintype.card ((j : Fin X.m) × (Fin (ar (X.sym j)) → A)) - (PSet p).card))
    w p h le_rfl
