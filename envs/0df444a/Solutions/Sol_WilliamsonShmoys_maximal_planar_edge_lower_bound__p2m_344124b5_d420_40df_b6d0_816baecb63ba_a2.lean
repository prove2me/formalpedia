-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_344124b5_d420_40df_b6d0_816baecb63ba_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:41.978392+00:00
-- url     : https://prove2.me/submissions/cf4ead38-ddd0-4495-af65-6c125ca17fbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    (∀ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset →
      HasPlanarDrawingOn K →
      K.edgeFinset ⊆ H.edgeFinset) →
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by
  classical
  intro hMax
  obtain ⟨K, hHK, hK, hExact⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_9fa2b5a7_e492_409e_9c7c_44f6f21de4a2_a3
      H hcard hH
  have hKH := hMax K hHK hK
  have hEq : H.edgeFinset = K.edgeFinset := Finset.Subset.antisymm hHK hKH
  rw [← hEq] at hExact
  omega