-- Prove2me | solution 1 for WilliamsonShmoys.finite_vertex_pair_list__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:13:56.028108+00:00
-- url     : https://prove2.me/submissions/35433d68-9b02-4d94-8dc1-580da865a1dd

import Mathlib

theorem solution {V : Type} [Fintype V] :
    ∃ pairs : List (V × V), ∀ u v : V, (u, v) ∈ pairs := by
  classical
  refine ⟨(Finset.univ.product Finset.univ).toList, ?_⟩
  intro u v
  simp
