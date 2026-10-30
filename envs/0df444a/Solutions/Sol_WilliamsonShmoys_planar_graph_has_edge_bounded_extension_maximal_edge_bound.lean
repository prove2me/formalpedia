-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_edge_bounded_extension_maximal_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:08:03.864874+00:00
-- url     : https://prove2.me/submissions/954509b7-7084-4991-a223-1b557b462b1d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLdraw, hLcount⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_triangulated_extension_f4cab8f1_36b2_49a4_9100_a8a3956b9d6e
      K hKdraw hCard
  have hLK : L = K := hKmax L hKL hLdraw
  subst L
  omega