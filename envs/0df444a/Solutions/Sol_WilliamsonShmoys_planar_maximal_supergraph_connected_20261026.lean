-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph_connected_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:43:35.661637+00:00
-- url     : https://prove2.me/submissions/81b1fd71-062e-4b22-8341-aea1e988c36d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_planar_edge_extension_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    K.Connected := by
  by_contra hconn
  obtain ⟨L, hKL, hLplanar, hnotLK⟩ :=
    WilliamsonShmoys.planar_disconnected_has_planar_edge_extension_20261026
      K hK hconn hV
  exact hnotLK (hmax L hKL hLplanar)