-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_graph_has_drawable_extension__p2m_a76ab648_9831_4644_9b76_244e5b3cfa82_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:54.702541+00:00
-- url     : https://prove2.me/submissions/66a137cc-77ff-474a-8021-6272cb3c5715

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V),
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ¬ K.Connected →
        ∃ M : SimpleGraph V,
          K.edgeSet ⊆ M.edgeSet ∧
          WilliamsonShmoys.HasPlanarDrawingOn M ∧
          ¬ M.edgeSet ⊆ K.edgeSet) := by
  intro h
  let K : SimpleGraph Empty := ⊥
  have hK : WilliamsonShmoys.HasPlanarDrawingOn K := by
    refine ⟨(fun v : Empty => v.elim), (fun u : Empty => u.elim), ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      cases a
    · intro u v huv hadj
      cases u
    · intro u v x y huv hxy hadj hadj' hne t ht s hs heq
      cases u
  have hdis : ¬ K.Connected := by
    intro hc
    exact isEmptyElim (Classical.choice hc.nonempty)
  obtain ⟨M, hsub, hM, hstrict⟩ := h (V := Empty) K hK hdis
  have hEq : M = K := Subsingleton.elim M K
  subst M
  exact hstrict Set.Subset.rfl