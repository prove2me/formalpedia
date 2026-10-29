-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_repair_271d2eb8_0883_4afb_88e9_925bc682e12d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:50:42.461006+00:00
-- url     : https://prove2.me/submissions/ed278507-8876-472b-91b2-9482f42f10e2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_exists

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hLcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_exists K hV hKplanar
  have hLK : L = K := hKmax L hKL hLplanar
  subst L
  exact hLcount