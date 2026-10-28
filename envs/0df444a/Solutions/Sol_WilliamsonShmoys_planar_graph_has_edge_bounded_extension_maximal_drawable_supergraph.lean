-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:02:32.156963+00:00
-- url     : https://prove2.me/submissions/289ad46a-047b-4f7b-9fea-4ffc9b17730b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_extension_maximizing_adjacencies
import Theorems.Thm_WilliamsonShmoys_strict_adjacency_pair_count_of_strict_graph_inclusion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      And (LE.le N K) (And (HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, LE.le K L -> HasPlanarDrawingOn L -> L = K)) := by
  obtain ⟨K, hNK, hKdraw, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_extension_maximizing_adjacencies N hNdraw
  refine ⟨K, hNK, hKdraw, ?_⟩
  intro L hKL hLdraw
  by_contra hne
  have hlt := WilliamsonShmoys.strict_adjacency_pair_count_of_strict_graph_inclusion K L hKL hne
  have hle := hmax L (le_trans hNK hKL) hLdraw
  omega