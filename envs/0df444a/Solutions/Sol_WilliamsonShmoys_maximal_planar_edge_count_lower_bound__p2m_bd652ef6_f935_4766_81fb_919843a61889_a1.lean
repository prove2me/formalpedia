-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_bd652ef6_f935_4766_81fb_919843a61889_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:11.643908+00:00
-- url     : https://prove2.me/submissions/56332802-a3c3-43fb-be30-2e1dde1106a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hV : 3 ≤ Fintype.card V)
    (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z →
      WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) :
    3 * Fintype.card V ≤ Y.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZ, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_d166c073_f098_437a_9518_b472263b9dd9_a1
      Y hY hV
  have hZY : Z = Y := hYmax Z hYZ hZ
  subst Z
  omega