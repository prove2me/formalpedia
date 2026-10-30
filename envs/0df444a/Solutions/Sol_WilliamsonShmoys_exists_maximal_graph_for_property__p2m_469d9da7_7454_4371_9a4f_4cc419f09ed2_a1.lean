-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_graph_for_property__p2m_469d9da7_7454_4371_9a4f_4cc419f09ed2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:02.9335+00:00
-- url     : https://prove2.me/submissions/77b37d59-0c71-4822-95fe-49c546aff151

import Mathlib

set_option autoImplicit false

theorem maxext {V : Type} [Fintype V] (R : SimpleGraph V → Prop) (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet ∧ R N ∧
      ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → R P → P = N := by
  classical
  have hfin : Finite (SimpleGraph V) := inferInstance
  obtain ⟨N, hN, hmax⟩ := Set.Finite.exists_maximalFor (f := id) (s := {G : SimpleGraph V | M ≤ G ∧ R G})
    (Set.toFinite _) ⟨M, le_rfl, hM⟩
  refine ⟨N, SimpleGraph.edgeSet_mono hN.1, hN.2, fun P hP hRP => ?_⟩
  have hle : N ≤ P := by
    intro u v h
    have : s(u, v) ∈ P.edgeSet := hP (by simpa using h)
    simpa using this
  exact le_antisymm (hmax ⟨hN.1.trans hle, hRP⟩ hle) hle |>.symm.symm

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : R M) : ∃ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet ∧ R N ∧ ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → R P → P = N := maxext R M hM
