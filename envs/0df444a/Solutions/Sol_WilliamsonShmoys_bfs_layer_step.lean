-- Prove2me | solution 1 for WilliamsonShmoys.bfs_layer_step
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T16:02:59.566283+00:00
-- url     : https://prove2.me/submissions/e2202d29-b73f-4f8e-886e-3b3951d278d4

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} (G : SimpleGraph V) (r w : V) (t : ℕ)
    (hw : ¬ (G.Reachable r w ∧ G.dist r w ≤ t)) :
    (G.Reachable r w ∧ G.dist r w = t + 1) ↔
      ∃ u, G.Reachable r u ∧ G.dist r u = t ∧ G.Adj u w := by
  constructor
  · rintro ⟨hrw, hd⟩
    obtain ⟨p, hp⟩ := hrw.exists_walk_length_eq_dist
    rw [hd] at hp
    -- the reversed walk starts with an edge `w ~ u`
    cases hq : p.reverse with
    | nil =>
      exfalso
      have := congrArg SimpleGraph.Walk.length hq
      simp only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_nil] at this
      omega
    | @cons _ u _ hadj q =>
      have hlen : q.length = t := by
        have := congrArg SimpleGraph.Walk.length hq
        simp [SimpleGraph.Walk.length_reverse] at this
        omega
      have hru : G.Reachable r u := ⟨q.reverse⟩
      have hle : G.dist r u ≤ t := by
        have := SimpleGraph.dist_le q.reverse
        rw [SimpleGraph.Walk.length_reverse, hlen] at this
        exact this
      have hge : t ≤ G.dist r u := by
        by_contra hlt
        push_neg at hlt
        obtain ⟨q', hq'⟩ := hru.exists_walk_length_eq_dist
        have := SimpleGraph.dist_le (q'.concat hadj.symm)
        rw [SimpleGraph.Walk.length_concat, hq'] at this
        exact hw ⟨hrw, by omega⟩
      exact ⟨u, hru, le_antisymm hle hge, hadj.symm⟩
  · rintro ⟨u, hru, hdu, hadj⟩
    have hrw : G.Reachable r w := hru.trans hadj.reachable
    refine ⟨hrw, ?_⟩
    obtain ⟨q', hq'⟩ := hru.exists_walk_length_eq_dist
    have h1 := SimpleGraph.dist_le (q'.concat hadj)
    rw [SimpleGraph.Walk.length_concat, hq', hdu] at h1
    have h2 : ¬ G.dist r w ≤ t := fun h => hw ⟨hrw, h⟩
    omega
