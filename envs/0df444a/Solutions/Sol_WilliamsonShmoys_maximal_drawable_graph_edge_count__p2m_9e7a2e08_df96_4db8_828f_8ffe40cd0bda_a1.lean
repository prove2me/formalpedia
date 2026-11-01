-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:45.535052+00:00
-- url     : https://prove2.me/submissions/df86b654-c596-4b45-a0dc-8cb480b6d7b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       U.edgeFinset ⊆ T.edgeFinset)) :
    letI : DecidableRel T.Adj := dT
    T.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel T.Adj := dT
  obtain ⟨U, dU, hU, hTU, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_fcf1b814_7848_4586_9efd_023714441148_a1
      T dT hT hn
  letI : DecidableRel U.Adj := dU
  have hUT : U.edgeFinset ⊆ T.edgeFinset := hmax U dU hU hTU
  have heq : T.edgeFinset = U.edgeFinset := Finset.Subset.antisymm hTU hUT
  rw [heq]
  exact hcard