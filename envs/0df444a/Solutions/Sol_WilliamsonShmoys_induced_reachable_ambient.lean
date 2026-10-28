-- Prove2me | solution 1 for WilliamsonShmoys.induced_reachable_ambient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:27:43.983552+00:00
-- url     : https://prove2.me/submissions/7f7b8d3d-bfd8-4af1-8712-983c534c2fb1

import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem solution {n : Nat} (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (u v : {x : Fin n // x ∈ S}) : (G.induce S).Reachable u v → G.Reachable v.1 u.1 := by
  intro h
  exact (h.map (SimpleGraph.Embedding.induce S).toHom).symm
