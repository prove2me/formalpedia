-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_cbd57c51e3344f4e814f42afaa7d171b
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:45:59.188351+00:00
-- url     : https://prove2.me/submissions/54f1467a-ff06-4c84-8655-cba2d760df31

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_d73146df_f66d_4d86_a4dc_57d1ab40d600_v3 H hH hV
  have hEq : K.edgeSet = H.edgeSet := hMax K hHK hK
  have hcard : K.edgeSet.ncard = H.edgeSet.ncard :=
    congrArg (fun s : Set (Sym2 V) => s.ncard) hEq
  simpa [hcard] using hcount