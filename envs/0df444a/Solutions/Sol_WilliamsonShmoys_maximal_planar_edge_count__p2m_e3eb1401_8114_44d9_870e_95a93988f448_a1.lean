-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:01:34.361244+00:00
-- url     : https://prove2.me/submissions/f0058170-e8b4-4a46-a7b6-865ae0ba2638

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) →
      ∀ u v, M.Adj u v → L.Adj u v) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
     3 * Fintype.card V = L.edgeFinset.card + 6) := by
  classical
  obtain ⟨M, hM, hLM, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulating_extension__p2m_5080cd2f_42f1_4d04_bf29_e50a32f61412_a2
      L hV hL
  have hML : ∀ u v, M.Adj u v → L.Adj u v :=
    hmax M hM hLM
  have hEq : L = M := by
    ext u v
    exact ⟨hLM u v, hML u v⟩
  subst M
  simpa using hcount