-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:05:10.356494+00:00
-- url     : https://prove2.me/submissions/a6b4db15-4cb5-4450-9bcb-7df894deac15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → False)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hsub, hL, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulating_completion K hK hCard
  have hEq : K.edgeSet = L.edgeSet := by
    apply Set.Subset.antisymm hsub
    intro e he
    by_contra heK
    have hstrict : K.edgeSet ⊂ L.edgeSet := by
      constructor
      · exact hsub
      · intro hreverse
        exact heK (hreverse he)
    exact (hMax L hstrict hL).elim
  have hcard : K.edgeSet.ncard = L.edgeSet.ncard := congrArg Set.ncard hEq
  calc
    K.edgeSet.ncard + 6 = L.edgeSet.ncard + 6 := by rw [hcard]
    _ = 3 * Fintype.card V := hcount