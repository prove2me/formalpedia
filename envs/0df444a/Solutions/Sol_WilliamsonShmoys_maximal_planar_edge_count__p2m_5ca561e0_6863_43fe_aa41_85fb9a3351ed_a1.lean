-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:40.938199+00:00
-- url     : https://prove2.me/submissions/a234642a-ecb1-4edd-82e6-3be0f59d7830
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K)
    (hcard : 3 <= Fintype.card V) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : forall G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨L, hsub, hL, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
      K hcard hK
  have hKL : K ≤ L := SimpleGraph.edgeFinset_subset_edgeFinset.mp hsub
  have hEq : L = K := hmax L hKL hL
  rw [← hEq]
  exact hcount