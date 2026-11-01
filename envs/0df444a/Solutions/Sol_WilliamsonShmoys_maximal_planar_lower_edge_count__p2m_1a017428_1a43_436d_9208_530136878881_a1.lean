-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_lower_edge_count__p2m_1a017428_1a43_436d_9208_530136878881_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:23.401016+00:00
-- url     : https://prove2.me/submissions/1db14213-a11f-4679-911e-9d9e89f944b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      (forall {u v : V}, L.Adj u v -> M.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      (forall {u v : V}, M.Adj u v -> L.Adj u v)) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     3 * Fintype.card V - 6 <= L.edgeFinset.card) := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨M, hLM, hM, hTri⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_edge_bound__p2m_3c9e368f_61fd_4a93_9244_4b323cc9e3bc_a2
      L hL hcard
  have hML : forall {u v : V}, M.Adj u v -> L.Adj u v := hmax M hLM hM
  have hAdj : forall u v : V, M.Adj u v ↔ L.Adj u v := by
    intro u v
    exact Iff.intro hML hLM
  have hRel : M.Adj = L.Adj := by
    funext u v
    exact propext (hAdj u v)
  have hEq : M = L := SimpleGraph.ext hRel
  cases hEq
  simpa using hTri