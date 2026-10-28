-- Prove2me | solution 2 for SingleMachinePrec.IntervalChromatic.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:17.901347+00:00
-- url     : https://prove2.me/submissions/4548585c-2cd1-4696-8f45-1f52bb5c21bf

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder
import Theorems.Thm_SingleMachinePrec_IntervalChromatic_adjacent_four

-- carved verbatim out of submission 1fc297aa-20db-44b8-bcc9-3b47bd595088, lines 198-202

section
set_option autoImplicit false
open SingleMachinePrec.IntervalChromatic

lemma inc {n : ℕ} (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    SingleMachinePrec.Framework.Incomparable (I n) (endpointPair a b hab) (endpointPair b c hbc) := by
  constructor
  · rintro (h | h)
    · have ha : a ∈ (endpointPair b c hbc).1 := h ▸ (by simp [endpointPair])
      simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact lt_irrefl _ hab
      · exact lt_asymm hab hbc
    · exact lt_irrefl b (h b (by simp [endpointPair]) b (by simp [endpointPair]))
  · rintro (h | h)
    · have ha : a ∈ (endpointPair b c hbc).1 := h ▸ (by simp [endpointPair])
      simp only [endpointPair, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact lt_irrefl _ hab
      · exact lt_asymm hab hbc
    · exact lt_irrefl b (h b (by simp [endpointPair]) b (by simp [endpointPair]))

open Classical in
noncomputable def S {n k : ℕ} (color : IncomparablePair (I n) → Fin k) (j l : Fin n) :
    Finset (Fin k) :=
  Finset.univ.filter (fun c => ∃ (i : Fin n) (h1 : i < j) (h2 : j < l),
    color ⟨(endpointPair i j h1, endpointPair j l h2), inc i j l h1 h2⟩ = c)

lemma adjc {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (i j l m : Fin n)
    (h1 : i < j) (h2 : j < l) (h3 : l < m) :
    color ⟨(endpointPair i j h1, endpointPair j l h2), inc i j l h1 h2⟩ ≠
    color ⟨(endpointPair j l h2, endpointPair l m h3), inc j l m h2 h3⟩ := by
  obtain ⟨a, b, hG⟩ := SingleMachinePrec.IntervalChromatic.adjacent_four i j l m h1 h2 h3
  exact hc _ _ hG

lemma S_ne {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (j l m : Fin n)
    (hjl : j < l) (hlm : l < m) : S color l m ≠ S color j l := by
  intro h
  have hmem : color ⟨(endpointPair j l hjl, endpointPair l m hlm),
      inc j l m hjl hlm⟩ ∈ S color l m := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hjl, hlm, rfl⟩
  rw [h] at hmem
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨i, h1, h2, he⟩ := hmem
  exact adjc color hc i j l m h1 h2 hlm he

open Classical in
noncomputable def Phi {n k : ℕ} (color : IncomparablePair (I n) → Fin k) (l : Fin n) :
    Finset (Finset (Fin k)) :=
  Finset.univ.filter (fun s => ∃ j : Fin n, j < l ∧ S color j l = s)

lemma Phi_ne {n k : ℕ} (color : IncomparablePair (I n) → Fin k)
    (hc : ∀ u v, G (I n) u v → color u ≠ color v) (l m : Fin n) (hlm : l < m) :
    Phi color l ≠ Phi color m := by
  intro h
  have hmem : S color l m ∈ Phi color m := by
    simp only [Phi, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, hlm, rfl⟩
  rw [← h] at hmem
  simp only [Phi, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨j, hj, hS⟩ := hmem
  exact S_ne color hc j l m hj hlm hS.symm

lemma not_col {n k : ℕ} (hn : 2 ^ (2 ^ k) < n) : ¬ Colorable n k := by
  rintro ⟨color, hc⟩
  have hinj : Function.Injective (Phi color) := by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (Phi_ne color hc a b h)
    · exact h
    · exact absurd hab.symm (Phi_ne color hc b a h)
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, Fintype.card_finset, Fintype.card_finset, Fintype.card_fin] at this
  exact absurd hn (not_lt.mpr this)

end

section
set_option autoImplicit false

open SingleMachinePrec.IntervalChromatic in
theorem solution (k : ℕ) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → ¬ Colorable n k := by
  refine ⟨2 ^ (2 ^ k) + 2, Nat.le_add_left 2 _, fun n hn => not_col ?_⟩
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by norm_num)) hn

end
