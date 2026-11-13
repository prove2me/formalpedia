-- Prove2me | solution 1 for TernarySync.Alphabet.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:14.173129+00:00
-- url     : https://prove2.me/submissions/54d1de2a-f776-41ef-aec8-f1fccbc5711c

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString
import Theorems.Thm_TernarySync_Alphabet_eq_3

section
set_option autoImplicit false

namespace TernarySync.Dev.Lemma22
open TernarySync.Alphabet

theorem lcs_set_bdd {α : Type*} (x y : List α) :
    BddAbove {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k} :=
  ⟨x.length, by rintro k ⟨z, hz, -, rfl⟩; exact hz.length_le⟩

theorem le_lcs {α : Type*} {w x y : List α} (hx : w.Sublist x) (hy : w.Sublist y) :
    w.length ≤ lcs x y :=
  le_csSup (lcs_set_bdd x y) ⟨w, hx, hy, rfl⟩

theorem lcs_attained {α : Type*} (x y : List α) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = lcs x y :=
  Nat.sSup_mem (s := {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k})
    ⟨0, [], by simp, by simp, rfl⟩ (lcs_set_bdd x y)

theorem lcs_le_left {α : Type*} (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hz, -, h⟩ := lcs_attained x y
  rw [← h]; exact hz.length_le

theorem lcs_le_right {α : Type*} (x y : List α) : lcs x y ≤ y.length := by
  obtain ⟨z, -, hz, h⟩ := lcs_attained x y
  rw [← h]; exact hz.length_le

theorem lcs_append_left {α : Type*} (A' A0 B : List α) :
    lcs (A' ++ A0) B ≤ A'.length + lcs A0 B := by
  obtain ⟨w, h1, h2, h⟩ := lcs_attained (A' ++ A0) B
  obtain ⟨w1, w2, rfl, h3, h4⟩ := List.sublist_append_iff.1 h1
  have e := le_lcs h4 ((List.sublist_append_right w1 w2).trans h2)
  have := h3.length_le
  simp at h
  omega

theorem lcs_append_right {α : Type*} (A B0 B' : List α) :
    lcs A (B0 ++ B') ≤ lcs A B0 + B'.length := by
  obtain ⟨w, h1, h2, h⟩ := lcs_attained A (B0 ++ B')
  obtain ⟨w1, w2, rfl, h3, h4⟩ := List.sublist_append_iff.1 h2
  have e := le_lcs ((List.sublist_append_left w1 w2).trans h1) h3
  have := h4.length_le
  simp at h
  omega

theorem factor_append {α : Type*} (S : List α) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    factor S i k = factor S i j ++ factor S j k := by
  unfold factor
  rw [show k - i = (j - i) + (k - j) by omega, List.take_add, List.drop_drop,
    show i + (j - i) = j by omega]

theorem factor_length {α : Type*} (S : List α) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ S.length) :
    (factor S i j).length = j - i := by
  unfold factor
  simp
  omega

theorem key (δ η m z E : ℝ) (hη : 0 < η) (hδ : 0 < δ) (hδη : δ * (2 + η) < η) (hm : 0 < m)
    (hz : 0 ≤ z) (h1 : z ≤ E) (h2 : 2 * η * m - z ≤ E) : δ * (2 * m + z) < E := by
  have hp : 0 < 2 * m + z := by linarith
  have h3 : (2 + η) * (δ * (2 * m + z)) < η * (2 * m + z) := by
    have := mul_lt_mul_of_pos_right hδη hp
    linarith
  rcases le_total (η * m) z with h | h
  · have h4 : η * (2 * m + z) ≤ (2 + η) * z := by nlinarith
    have h5 : (2 + η) * (δ * (2 * m + z)) < (2 + η) * E := by nlinarith
    exact lt_of_mul_lt_mul_left h5 (by linarith)
  · have h4 : η * (2 * m + z) ≤ (2 + η) * (2 * η * m - z) := by nlinarith
    have h5 : (2 + η) * (δ * (2 * m + z)) < (2 + η) * E := by nlinarith
    exact lt_of_mul_lt_mul_left h5 (by linarith)

theorem sync_core {α : Type*} (S : List α) (η : ℝ) (hη0 : 0 < η)
    (h4 : ∀ t ℓ : ℕ, 1 ≤ ℓ → t + 2 * ℓ ≤ S.length →
      (lcs (factor S t (t + ℓ)) (factor S (t + ℓ) (t + 2 * ℓ)) : ℝ) ≤ (1 - η) * (ℓ : ℝ))
    (ε : ℝ) (hε1 : ε < 1) (hε : 1 - ε < η / (2 + η)) : IsSyncString ε S := by
  intro i j k hij hjk hk
  set m := min (j - i) (k - j) with hm
  have hm1 : 1 ≤ m := by omega
  have hmA : m ≤ j - i := min_le_left _ _
  have hmB : m ≤ k - j := min_le_right _ _
  have hsplitA := factor_append S i (j - m) j (by omega) (by omega)
  have hsplitB := factor_append S j (j + m) k (by omega) (by omega)
  have hH := h4 (j - m) m hm1 (by omega)
  rw [show j - m + m = j by omega, show j - m + 2 * m = j + m by omega] at hH
  have hlA := factor_length S i (j - m) (by omega) (by omega)
  have hlB := factor_length S (j + m) k (by omega) (by omega)
  have hlA' := factor_length S i j (by omega) (by omega)
  have hlB' := factor_length S j k (by omega) (by omega)
  have hL : lcs (factor S i j) (factor S j k) ≤ (j - m - i) +
      lcs (factor S (j - m) j) (factor S j (j + m)) + (k - j - m) := by
    have e1 := lcs_append_left (factor S i (j - m)) (factor S (j - m) j) (factor S j k)
    have e2 := lcs_append_right (factor S (j - m) j) (factor S j (j + m)) (factor S (j + m) k)
    rw [hsplitA, hsplitB]
    rw [hsplitB] at e1
    omega
  have hLm : lcs (factor S i j) (factor S j k) ≤ m := by
    have := lcs_le_left (factor S i j) (factor S j k)
    have := lcs_le_right (factor S i j) (factor S j k)
    omega
  have hed := TernarySync.Alphabet.eq_3 (factor S i j) (factor S j k)
  have hedR : (ed (factor S i j) (factor S j k) : ℝ) =
      ((j - i : ℕ) : ℝ) + ((k - j : ℕ) : ℝ) - 2 * (lcs (factor S i j) (factor S j k) : ℝ) := by
    rw [hlA', hlB'] at hed
    exact_mod_cast hed
  obtain ⟨p, hp⟩ : ∃ p, j = i + m + p := ⟨j - m - i, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, k = j + m + q := ⟨k - j - m, by omega⟩
  have hpq : p = 0 ∨ q = 0 := by omega
  have e3 : j - m - i = p := by omega
  have e4 : k - j - m = q := by omega
  rw [e3, e4] at hL
  have hc : (lcs (factor S (j - m) j) (factor S j (j + m)) : ℝ) ≤ (1 - η) * (m : ℝ) := hH
  have hLR : (lcs (factor S i j) (factor S j k) : ℝ) ≤ (p : ℝ) +
      (lcs (factor S (j - m) j) (factor S j (j + m)) : ℝ) + (q : ℝ) := by exact_mod_cast hL
  have hLmR : (lcs (factor S i j) (factor S j k) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hLm
  have ea : ((j - i : ℕ) : ℝ) = (m : ℝ) + p := by
    have : j - i = m + p := by omega
    rw [this]; push_cast; ring
  have eb : ((k - j : ℕ) : ℝ) = (m : ℝ) + q := by
    have : k - j = m + q := by omega
    rw [this]; push_cast; ring
  have ek : ((k : ℝ) - (i : ℝ)) = 2 * (m : ℝ) + ((p : ℝ) + q) := by
    have : k = i + m + p + m + q := by omega
    rw [this]; push_cast; ring
  rw [ek]
  rw [ea, eb] at hedR
  have hδ : 0 < 1 - ε := by linarith
  have hδη : (1 - ε) * (2 + η) < η := by
    have h2 : (0 : ℝ) < 2 + η := by linarith
    rwa [lt_div_iff₀ h2] at hε
  refine key (1 - ε) η (m : ℝ) ((p : ℝ) + q) _ hη0 hδ hδη (by exact_mod_cast hm1)
    (by positivity) ?_ ?_
  · rw [hedR]; linarith
  · rw [hedR]; nlinarith

end TernarySync.Dev.Lemma22

namespace TernarySync.Alphabet
open TernarySync.Dev.Lemma22 in
theorem chk_lemma_2_2 {α : Type*} (S : List α) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (h4 : ∀ t ℓ : ℕ, 1 ≤ ℓ → t + 2 * ℓ ≤ S.length →
      (lcs (factor S t (t + ℓ)) (factor S (t + ℓ) (t + 2 * ℓ)) : ℝ) ≤ (1 - η) * (ℓ : ℝ)) :
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 → 1 - ε < η / (2 + η) → IsSyncString ε S) ∧
      IsSyncString (1 - η / 3) S := by
  refine ⟨fun ε _ hε1 hε => sync_core S η hη0 h4 ε hε1 hε, ?_⟩
  refine sync_core S η hη0 h4 _ (by linarith) ?_
  have h2 : (0 : ℝ) < 2 + η := by linarith
  rw [lt_div_iff₀ h2]
  nlinarith
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_lemma_2_2 := @TernarySync.Alphabet.chk_lemma_2_2
