-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:07.553602+00:00
-- url     : https://prove2.me/submissions/7c59338f-7e94-4d12-bd73-d14971b3c90c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ, Fintype.card V + f = J.edgeFinset.card + 2 := by
  classical
  by_cases hV : Nonempty V
  · have hpre : J.Preconnected := fun u v => hconn u v
    have hconnected : J.Connected :=
      (J.connected_iff_exists_forall_reachable).2
        ⟨Classical.choice hV, fun w => hpre _ w⟩
    have hb := hconnected.card_vert_le_card_edgeSet_add_one
    have hb' : Fintype.card V ≤ J.edgeFinset.card + 1 := by
      simpa only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] using hb
    refine ⟨J.edgeFinset.card + 1 - Fintype.card V + 1, ?_⟩
    omega
  · letI : IsEmpty V := not_nonempty_iff.mp hV
    have hJbot : J = ⊥ := by
      ext u v
      exact isEmptyElim u
    refine ⟨2, ?_⟩
    simp [hJbot]