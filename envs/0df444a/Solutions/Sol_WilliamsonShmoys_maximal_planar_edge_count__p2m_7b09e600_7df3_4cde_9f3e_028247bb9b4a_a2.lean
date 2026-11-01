-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_7b09e600_7df3_4cde_9f3e_028247bb9b4a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:16.5582+00:00
-- url     : https://prove2.me/submissions/79c342b8-2f57-47ac-a884-5b449fdd340c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V - 6 = H.edgeSet.ncard := by
  obtain ⟨K, hHK, hKplanar, hKcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_c4f1425b_0637_4d8f_adde_21996a629192_a2
      H hplanar hcard
  have hKH : K = H := hmax K hHK hKplanar
  rw [hKH] at hKcount
  exact hKcount.symm