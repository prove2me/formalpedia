-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_separated_by_unreachability__p2m_282a2a61_c7fa_4a1e_ac79_616c5409586a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:03.597621+00:00
-- url     : https://prove2.me/submissions/9cc0cc31-6e31-4c68-aa3c-40c824799c38

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hne : Nonempty V) (hdisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  classical
  by_contra h
  apply hdisconnected
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨Classical.choice hne, ?_⟩
  intro w
  by_contra hn
  exact h ⟨Classical.choice hne, w, hn⟩