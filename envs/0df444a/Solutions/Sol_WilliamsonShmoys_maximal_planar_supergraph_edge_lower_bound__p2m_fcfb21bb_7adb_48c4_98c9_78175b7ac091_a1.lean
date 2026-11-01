-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:42:07.593253+00:00
-- url     : https://prove2.me/submissions/292585d5-0cf0-4d09-9620-e0e83af03023
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hMax : forall P : SimpleGraph V,
      (forall {u v : V}, N.Adj u v -> P.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V - 6 <= N.edgeFinset.card) := by
  obtain ⟨P, hNP, hP, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_tight_edges__p2m_b575e78e_3e28_4118_93fc_258c931bc299_a1
      N hN hcard
  have hPN : P = N := hMax P hNP hP
  subst P
  omega