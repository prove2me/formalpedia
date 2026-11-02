-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:58:50.058998+00:00
-- url     : https://prove2.me/submissions/64d7752e-761c-408c-9716-ac11cce9caa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hSparse : (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 < 3 * Fintype.card V)) :
    ∃ M : SimpleGraph V, L ≤ M ∧ M ≠ L ∧ HasPlanarDrawingOn M := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨M, hLM, hM, hMcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
      L hV hL
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hMcard' : M.edgeFinset.card + 6 = 3 * Fintype.card V := by
    simpa using hMcard
  have hSparse' : L.edgeFinset.card + 6 < 3 * Fintype.card V := by
    simpa using hSparse
  refine ⟨M, hLM, ?_, hM⟩
  intro hEq
  subst M
  rw [hMcard'] at hSparse'
  omega