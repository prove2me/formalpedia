-- Prove2me | solution 1 for TwinWidthI.GridThm.theorem_5_4_first
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:28:21.339175+00:00
-- url     : https://prove2.me/submissions/0096e7e1-57d4-4bdd-b0aa-ae55ddb81cee

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

open Finset TwinWidthI.GridThm

namespace TwinWidthI.GridThm.Theorem54FirstProof

private lemma not_isVertical_of_subset {A : Type*} {n m : ℕ}
    {M : Matrix (Fin n) (Fin m) A} {X₁ X₂ : Finset (Fin n)} {Y : Finset (Fin m)}
    (hsub : X₁ ⊆ X₂) (h : ¬ IsVertical M X₁ Y) : ¬ IsVertical M X₂ Y := by
  intro h2
  exact h (fun i hi i' hi' j hj => h2 i (hsub hi) i' (hsub hi') j hj)

private lemma not_isVertical_transpose_of_not_isHorizontal {A : Type*} {n m : ℕ}
    {M : Matrix (Fin n) (Fin m) A} {X : Finset (Fin n)} {Y₁ Y₂ : Finset (Fin m)}
    (hsub : Y₁ ⊆ Y₂) (h : ¬ IsHorizontal M X Y₁) :
    ¬ IsVertical M.transpose Y₂ X := by
  intro h2
  exact h (fun i hi j hj j' hj' => h2 j (hsub hj) j' (hsub hj') i hi)

private lemma zoneConst_transpose_iff {A : Type*} {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    ZoneConst M.transpose Y X ↔ ZoneConst M X Y := by
  constructor
  · intro h i hi i' hi' j hj j' hj'
    exact h j hj j' hj' i hi i' hi'
  · intro h j hj j' hj' i hi i' hi'
    exact h i hi i' hi' j hj j' hj'

open Classical in
private lemma not_exists_cutPart_subset {A : Type*} {n m t : ℕ}
    (M : Matrix (Fin n) (Fin m) A)
    (X : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m)))
    (c : Fin (2 * t + 2 + 1) → ℕ)
    (hc_mono : StrictMono c)
    (hC_div : IsDivision C)
    (herr : #{Y ∈ C.parts | ¬ ZoneConst M X Y} ≤ t)
    (hX_not_vert : ∀ b : Fin (2 * t + 2), ¬ IsVertical M X (cutPart c b))
    (hC_not_sub : ∀ b : Fin (2 * t + 2), ∀ Y ∈ C.parts, ¬ (cutPart c b ⊆ Y)) :
    False := by
  let b : Fin (t + 1) → Fin (2 * t + 2) := fun u => ⟨2 * u.val, by omega⟩
  have hex : ∀ u : Fin (t + 1), ∃ j ∈ cutPart c (b u), ∃ i₁ ∈ X, ∃ i₂ ∈ X, M i₁ j ≠ M i₂ j := by
    intro u
    have hnv := hX_not_vert (b u)
    unfold IsVertical at hnv
    push Not at hnv
    rcases hnv with ⟨i₁, hi₁, i₂, hi₂, j, hj, hne⟩
    exact ⟨j, hj, i₁, hi₁, i₂, hi₂, hne⟩
  choose j hj_cut h_witness using hex
  let Y : Fin (t + 1) → Finset (Fin m) := fun u => C.part (j u)
  have hY_mem : ∀ u : Fin (t + 1), Y u ∈ C.parts :=
    fun u => C.part_mem.mpr (mem_univ (j u))
  have hj_in_Y : ∀ u : Fin (t + 1), j u ∈ Y u :=
    fun u => C.mem_part (mem_univ (j u))
  have hY_not_const : ∀ u : Fin (t + 1), ¬ ZoneConst M X (Y u) := by
    intro u hconst
    rcases h_witness u with ⟨i₁, hi₁, i₂, hi₂, hne⟩
    exact hne (hconst i₁ hi₁ i₂ hi₂ (j u) (hj_in_Y u) (j u) (hj_in_Y u))
  have hY_in_bad : ∀ u : Fin (t + 1), Y u ∈ {Z ∈ C.parts | ¬ ZoneConst M X Z} :=
    fun u => mem_filter.mpr ⟨hY_mem u, hY_not_const u⟩
  have h_lt_false : ∀ {u₁ u₂ : Fin (t + 1)}, u₁ < u₂ → Y u₁ = Y u₂ → False := by
    intro u₁ u₂ hu hYeq
    let b_mid : Fin (2 * t + 2) := ⟨2 * u₁.val + 1, by omega⟩
    apply hC_not_sub b_mid (Y u₁) (hY_mem u₁)
    intro x hx
    have hj₁_cut := hj_cut u₁
    have hj₂_cut := hj_cut u₂
    simp only [cutPart, mem_filter, mem_univ, true_and] at hj₁_cut hj₂_cut hx
    have h_eq1 : (b u₁).succ = b_mid.castSucc := by
      ext
      simp [b, b_mid]
    have h_le2 : b_mid.succ ≤ (b u₂).castSucc := by
      rw [Fin.le_iff_val_le_val]
      change 2 * u₁.val + 1 + 1 ≤ 2 * u₂.val
      omega
    have hj₁_le_x : j u₁ ≤ x := by
      rw [Fin.le_iff_val_le_val]
      have h1 : (j u₁ : ℕ) < c b_mid.castSucc := h_eq1 ▸ hj₁_cut.2
      omega
    have hx_le_j₂ : x ≤ j u₂ := by
      rw [Fin.le_iff_val_le_val]
      have h2 : c b_mid.succ ≤ c (b u₂).castSucc := hc_mono.monotone h_le2
      omega
    have hj₂_in_Yu₁ : j u₂ ∈ Y u₁ := hYeq.symm ▸ hj_in_Y u₂
    exact hC_div (Y u₁) (hY_mem u₁) (j u₁) (hj_in_Y u₁) (j u₂) hj₂_in_Yu₁ x hj₁_le_x hx_le_j₂
  have hY_inj : Set.InjOn Y (univ : Finset (Fin (t + 1))) := by
    intro u₁ _ u₂ _ hYeq
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · exact False.elim (h_lt_false hlt hYeq)
    · rfl
    · exact False.elim (h_lt_false hgt hYeq.symm)
  have hcard : (univ : Finset (Fin (t + 1))).card ≤ #{Z ∈ C.parts | ¬ ZoneConst M X Z} :=
    card_le_card_of_injOn Y (fun u _ => hY_in_bad u) hY_inj
  rw [card_univ, Fintype.card_fin] at hcard
  omega

end TwinWidthI.GridThm.Theorem54FirstProof

open TwinWidthI.GridThm.Theorem54FirstProof

theorem solution {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (t : ℕ)
    (h : TwinOrdered M t) : MixedFree M (2 * t + 2) := by
  classical
  intro hmix
  rcases h with ⟨N, R, C, hR0, hC0, hRN, hCN, hstep, hinv⟩
  rcases hmix with ⟨r, c, hr, hc, hmixed⟩
  let K := 2 * t + 2
  let a₀ : Fin K := ⟨0, by omega⟩
  let b₀ : Fin K := ⟨0, by omega⟩
  let P : Fin (N + 1) → Prop := fun k =>
    (∃ a : Fin K, ∃ X ∈ (R k).parts, cutPart r a ⊆ X) ∨
    (∃ b : Fin K, ∃ Y ∈ (C k).parts, cutPart c b ⊆ Y)
  have hP0 : ¬ P 0 := by
    rintro (⟨a, X, hX, hsub⟩ | ⟨b, Y, hY, hsub⟩)
    · rw [hR0, Finpartition.mem_bot_iff] at hX
      rcases hX with ⟨x, _, rfl⟩
      have hnv := (hmixed a b₀).1
      unfold IsVertical at hnv
      push Not at hnv
      rcases hnv with ⟨i₁, hi₁, i₂, hi₂, j, _, hne⟩
      have hi₁' : i₁ = x := mem_singleton.mp (hsub hi₁)
      have hi₂' : i₂ = x := mem_singleton.mp (hsub hi₂)
      exact hne (by rw [hi₁', hi₂'])
    · rw [hC0, Finpartition.mem_bot_iff] at hY
      rcases hY with ⟨y, _, rfl⟩
      have hnh := (hmixed a₀ b).2
      unfold IsHorizontal at hnh
      push Not at hnh
      rcases hnh with ⟨i, _, j₁, hj₁, j₂, hj₂, hne⟩
      have hj₁' : j₁ = y := mem_singleton.mp (hsub hj₁)
      have hj₂' : j₂ = y := mem_singleton.mp (hsub hj₂)
      exact hne (by rw [hj₁', hj₂'])
  have hPN : P (Fin.last N) := by
    left
    have hnv := (hmixed a₀ b₀).1
    unfold IsVertical at hnv
    push Not at hnv
    rcases hnv with ⟨i₀, hi₀, _, _, _, _, _⟩
    refine ⟨a₀, (R (Fin.last N)).part i₀, (R (Fin.last N)).part_mem.mpr (mem_univ i₀), ?_⟩
    intro i hi
    have h_eq : (R (Fin.last N)).part i = (R (Fin.last N)).part i₀ :=
      Finset.card_le_one_iff.mp hRN
        ((R (Fin.last N)).part_mem.mpr (mem_univ i))
        ((R (Fin.last N)).part_mem.mpr (mem_univ i₀))
    rw [← h_eq]
    exact (R (Fin.last N)).mem_part (mem_univ i)
  have hstep_not : ∀ idx : Fin N, ¬ P idx.castSucc → ¬ P idx.succ := by
    intro idx hnot hsucc
    have hnotR : ∀ a : Fin K, ∀ X ∈ (R idx.castSucc).parts, ¬ (cutPart r a ⊆ X) :=
      fun a X hX hsub => hnot (Or.inl ⟨a, X, hX, hsub⟩)
    have hnotC : ∀ b : Fin K, ∀ Y ∈ (C idx.castSucc).parts, ¬ (cutPart c b ⊆ Y) :=
      fun b Y hY hsub => hnot (Or.inr ⟨b, Y, hY, hsub⟩)
    rcases hstep idx with ⟨_, hCeq⟩ | ⟨hReq, _⟩
    · have hnotC_succ : ∀ b : Fin K, ∀ Y ∈ (C idx.succ).parts, ¬ (cutPart c b ⊆ Y) := by
        rw [hCeq]
        exact hnotC
      rcases hsucc with ⟨a, X, hX, hsub⟩ | ⟨b, Y, hY, hsub⟩
      · exact not_exists_cutPart_subset M X (C idx.succ) c hc.1 (hinv idx.succ).2.2
          ((hinv idx.succ).1.1 X hX)
          (fun b => not_isVertical_of_subset hsub (hmixed a b).1)
          hnotC_succ
      · exact hnotC_succ b Y hY hsub
    · have hnotR_succ : ∀ a : Fin K, ∀ X ∈ (R idx.succ).parts, ¬ (cutPart r a ⊆ X) := by
        rw [hReq]
        exact hnotR
      rcases hsucc with ⟨a, X, hX, hsub⟩ | ⟨b, Y, hY, hsub⟩
      · exact hnotR_succ a X hX hsub
      · have herr_trans : #{X ∈ (R idx.succ).parts | ¬ ZoneConst M.transpose Y X} ≤ t := by
          simp_rw [zoneConst_transpose_iff]
          exact (hinv idx.succ).1.2 Y hY
        exact not_exists_cutPart_subset M.transpose Y (R idx.succ) r hr.1 (hinv idx.succ).2.1
          herr_trans
          (fun a => not_isVertical_transpose_of_not_isHorizontal hsub (hmixed a b).2)
          hnotR_succ
  have hP_all : ∀ k (hk : k ≤ N), ¬ P ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro _
      exact hP0
    | succ k ih =>
      intro hk
      exact hstep_not ⟨k, Nat.lt_of_succ_le hk⟩ (ih (Nat.le_of_succ_le hk))
  exact hP_all N le_rfl hPN
