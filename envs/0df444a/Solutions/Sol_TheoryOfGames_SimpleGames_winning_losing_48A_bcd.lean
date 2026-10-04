-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.winning_losing_48A_bcd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:02:05.710976+00:00
-- url     : https://prove2.me/submissions/79c28460-9c28-46c7-8846-615fde6dcbdf

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

set_option autoImplicit false

open TheoryOfGames.SimpleGames in
theorem p2m_6e83dca5_sum_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (A : Finset (Fin n)) : ∑ k ∈ A, v {k} ≤ v A := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a A ha ih =>
    rw [Finset.sum_insert ha]
    have hd : Disjoint ({a} : Finset (Fin n)) A := Finset.disjoint_singleton_left.mpr ha
    have h := hv.2.2 {a} A hd
    rw [← Finset.insert_eq] at h
    linarith

open TheoryOfGames.SimpleGames in
theorem p2m_6e83dca5_flat_sub {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (S T : Finset (Fin n)) (hS : IsFlat v S) (hTS : T ⊆ S) : IsFlat v T := by
  classical
  unfold IsFlat at *
  have h1 := p2m_6e83dca5_sum_le v hv T
  have h2 := p2m_6e83dca5_sum_le v hv (S \ T)
  have hd : Disjoint T (S \ T) := Finset.disjoint_sdiff
  have h3 := hv.2.2 T (S \ T) hd
  rw [Finset.union_sdiff_of_subset hTS] at h3
  have h4 : ∑ k ∈ S, v {k} = ∑ k ∈ T, v {k} + ∑ k ∈ S \ T, v {k} := by
    rw [← Finset.sum_union hd, Finset.union_sdiff_of_subset hTS]
  linarith


open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    (∀ S : Finset (Fin n), S ∈ winningSets v ↔ Sᶜ ∈ losingSets v) ∧
    (∀ S T : Finset (Fin n), S ∈ winningSets v → S ⊆ T → T ∈ winningSets v) ∧
    (∀ S T : Finset (Fin n), S ∈ losingSets v → T ⊆ S → T ∈ losingSets v) := by
  refine ⟨fun S => Iff.rfl, ?_, ?_⟩
  · intro S T hS hST
    exact p2m_6e83dca5_flat_sub v hv Sᶜ Tᶜ hS (Finset.compl_subset_compl.mpr hST)
  · intro S T hS hTS
    exact p2m_6e83dca5_flat_sub v hv S T hS hTS
