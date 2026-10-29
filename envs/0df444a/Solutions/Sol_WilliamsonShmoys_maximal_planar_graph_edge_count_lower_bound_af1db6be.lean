-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_lower_bound_af1db6be
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:07:52.999231+00:00
-- url     : https://prove2.me/submissions/de174015-8d6f-43ef-911e-4893bd363d90

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hLplanar, hLbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound K hV hK
  have hLK : L = K := hmax L hKL hLplanar
  simpa [hLK] using hLbound
