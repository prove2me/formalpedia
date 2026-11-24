-- Prove2me | solution 1 for ReadOnceParityBP.LowerBound.path_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-23T23:38:02.752851+00:00
-- url     : https://prove2.me/submissions/430f3d7d-4757-4ada-9b04-6418e75810aa

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_LabelledDAG

set_option autoImplicit false

open ReadOnceParityBP.LowerBound

theorem sol_walk_append {m k : ℕ} (src tgt : Fin m → Fin k) (p q : List (Fin m))
    (u v : Fin k) :
    IsWalk src tgt (p ++ q) u v ↔ ∃ w, IsWalk src tgt p u w ∧ IsWalk src tgt q w v := by
  induction p generalizing u with
  | nil => simp [IsWalk]
  | cons e p ih =>
    simp only [List.cons_append, IsWalk, ih]
    constructor
    · rintro ⟨h1, w, h2, h3⟩
      exact ⟨w, ⟨h1, h2⟩, h3⟩
    · rintro ⟨w, ⟨h1, h2⟩, h3⟩
      exact ⟨h1, w, h2, h3⟩

theorem sol_walk_unique {m k : ℕ} (src tgt : Fin m → Fin k) (p : List (Fin m)) :
    ∀ u v v' : Fin k, IsWalk src tgt p u v → IsWalk src tgt p u v' → v = v' := by
  induction p with
  | nil =>
    intro u v v' h h'
    simp only [IsWalk] at h h'
    exact h.symm.trans h'
  | cons e p ih =>
    intro u v v' h h'
    simp only [IsWalk] at h h'
    exact ih (tgt e) v v' h.2 h'.2

theorem solution {L : Type} (G : LabelledDAG L) :
    G.stPaths.Finite := by
  apply (List.finite_length_le (Fin G.numE) G.numV).subset
  intro p hp
  simp only [Set.mem_setOf_eq]
  have hp' : IsWalk G.graph.tail G.graph.head p G.s G.t := hp
  have hex : ∀ i, ∃ w, IsWalk G.graph.tail G.graph.head (p.take i) G.s w := by
    intro i
    have h := hp'
    rw [← List.take_append_drop i p, sol_walk_append] at h
    obtain ⟨w, hw, -⟩ := h
    exact ⟨w, hw⟩
  choose w hw using hex
  have hne : ∀ i j, i < j → j ≤ p.length → w i ≠ w j := by
    intro i j hij hj heq
    have h := hw j
    rw [← List.take_append_drop i (p.take j), sol_walk_append] at h
    obtain ⟨u, hu1, hu2⟩ := h
    rw [List.take_take, min_eq_left hij.le] at hu1
    have hwu := sol_walk_unique _ _ _ _ _ _ (hw i) hu1
    rw [← hwu, heq] at hu2
    have hnil := G.acyclic _ _ hu2
    have hlen := congrArg List.length hnil
    simp only [List.length_drop, List.length_take, List.length_nil] at hlen
    omega
  by_contra hlen
  push_neg at hlen
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (p.length + 1) => w i) (by simp only [Fintype.card_fin]; omega)
  have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hab' with h | h
  · exact hne a b h (by have := b.isLt; omega) (by simpa using hfab)
  · exact hne b a h (by have := a.isLt; omega) (by simpa using hfab.symm)
