-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:28.428786+00:00
-- url     : https://prove2.me/submissions/65282f08-0c9f-40db-9450-b3ccfd700b16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hExt :=
    WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
      K hK hcard
  cases hExt with
  | intro L hExt =>
    cases hExt with
    | intro hKL hExt =>
      cases hExt with
      | intro hL htri =>
        have hLK : L = K := hmax L hKL hL
        cases hLK
        exact htri