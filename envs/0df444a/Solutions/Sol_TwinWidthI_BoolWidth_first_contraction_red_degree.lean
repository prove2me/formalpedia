-- Prove2me | solution 1 for TwinWidthI.BoolWidth.first_contraction_red_degree
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:02:37.504796+00:00
-- url     : https://prove2.me/submissions/e1e25a7d-8bb5-4e36-8176-d72586b60c79

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

set_option autoImplicit false
open Finset TwinWidthI.BoolWidth

theorem X_hom_single {V : Type*} (G : SimpleGraph V) (a b : V) :
    Homogeneous G {a} {b} := by
  by_cases h : G.Adj a b
  · left; simp [h]
  · right; simp [h]

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B) (hcover : A ∪ B = univ)
    (N : ℕ) (hA : #A ≤ 2 * N) (u v : V) (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v)
    (htwin : ∀ b ∈ B, (G.Adj u b ↔ G.Adj v b))
    (P : Finpartition (univ : Finset V))
    (hP : P.parts = insert {u, v} (((univ.erase u).erase v).image fun w => ({w} : Finset V))) :
    IsDPartition G P (2 * N - 1) := by
  classical
  have hcard2 : 2 ≤ #A := by
    have := Finset.one_lt_card.2 ⟨u, hu, v, hv, huv⟩
    omega
  intro X hX
  rw [hP] at hX
  rw [Finset.mem_insert, Finset.mem_image] at hX
  rcases hX with rfl | ⟨w, hw, rfl⟩
  · -- the contracted part {u, v}
    have hsub : (P.parts.filter (fun Y => Y ≠ {u, v} ∧ ¬ Homogeneous G {u, v} Y)) ⊆
        ((A.erase u).erase v).image (fun w => ({w} : Finset V)) := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      obtain ⟨hYP, hYne, hYnh⟩ := hY
      rw [hP, Finset.mem_insert, Finset.mem_image] at hYP
      rcases hYP with h | ⟨w', hw', rfl⟩
      · exact absurd h hYne
      · rw [Finset.mem_image]
        refine ⟨w', ?_, rfl⟩
        have hw'u : w' ≠ u := fun h => by simp [h] at hw'
        have hw'v : w' ≠ v := fun h => by simp [h] at hw'
        have hw'A : w' ∈ A := by
          by_contra hnA
          have hB : w' ∈ B := by
            have : w' ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ _
            rcases Finset.mem_union.1 this with h | h
            · exact absurd h hnA
            · exact h
          apply hYnh
          have ht := htwin w' hB
          by_cases h : G.Adj u w'
          · left; intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> subst hy
            · exact h
            · exact ht.1 h
          · right; intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> subst hy
            · exact h
            · exact fun h' => h (ht.2 h')
        simp [hw'A, hw'u, hw'v]
    calc #(P.parts.filter (fun Y => Y ≠ {u, v} ∧ ¬ Homogeneous G {u, v} Y))
        ≤ #(((A.erase u).erase v).image (fun w => ({w} : Finset V))) := Finset.card_le_card hsub
      _ ≤ #((A.erase u).erase v) := Finset.card_image_le
      _ ≤ 2 * N - 1 := by
        rw [Finset.card_erase_of_mem (by simp [hv, huv.symm]), Finset.card_erase_of_mem hu]
        omega
  · -- a singleton part
    have hsub : (P.parts.filter (fun Y => Y ≠ {w} ∧ ¬ Homogeneous G {w} Y)) ⊆ {{u, v}} := by
      intro Y hY
      rw [Finset.mem_filter] at hY
      obtain ⟨hYP, hYne, hYnh⟩ := hY
      rw [hP, Finset.mem_insert, Finset.mem_image] at hYP
      rcases hYP with h | ⟨w', hw', rfl⟩
      · simp [h]
      · exact absurd (X_hom_single G w w') hYnh
    calc #(P.parts.filter (fun Y => Y ≠ {w} ∧ ¬ Homogeneous G {w} Y)) ≤ #({{u, v}} : Finset (Finset V)) :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ ≤ 2 * N - 1 := by omega
