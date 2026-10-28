-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_b74a49f4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:53:03.130398+00:00
-- url     : https://prove2.me/submissions/f2bf1972-ff20-4173-b524-15bc89ee0c66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_8e6fe4ee_76fd_4caa_8f38_7058c432af92
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_8e6fe4ee_76fd_4caa_8f38_7058c432af92 K hK
  obtain ⟨hMono, hCount⟩ :=
    WilliamsonShmoys.maximal_drawable_edge_count_8e6fe4ee_76fd_4caa_8f38_7058c432af92
      K H hKH hH hMax hCard
  exact ⟨H, hKH, hH, hMono, hCount⟩