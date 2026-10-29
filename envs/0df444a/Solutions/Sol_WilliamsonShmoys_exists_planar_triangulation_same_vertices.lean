-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:35:53.867708+00:00
-- url     : https://prove2.me/submissions/259660fa-0780-420a-9f2c-66a6659b5f0e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_finite_maximal_drawable_supergraph_e8a894df
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_e8a894df

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V, H <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Exists.elim
    (WilliamsonShmoys.exists_finite_maximal_drawable_supergraph_e8a894df H hH)
  intro K hKdata
  have hHK : H <= K := hKdata.1
  have hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K := hKdata.2.1
  have hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K := hKdata.2.2
  have hcount : K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_drawable_edge_count_e8a894df K hV hKdraw hmax
  exact Exists.intro K (And.intro hHK (And.intro hKdraw hcount))