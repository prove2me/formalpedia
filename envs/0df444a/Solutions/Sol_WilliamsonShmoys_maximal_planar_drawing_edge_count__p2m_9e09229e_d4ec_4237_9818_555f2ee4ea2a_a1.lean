-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_9e09229e_d4ec_4237_9818_555f2ee4ea2a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:13.673988+00:00
-- url     : https://prove2.me/submissions/66880fe7-09c5-4524-be65-c28e210a5438
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨H, hKH, hHd, hcount⟩ :=
    WilliamsonShmoys.planar_graph_extends_to_triangulation__p2m_f90853da_a441_4590_8374_63300059b95b_a1
      K hK hV
  have hHK : H ≤ K := hmax H hKH hHd
  have hEq : K = H := le_antisymm hKH hHK
  simpa [hEq] using hcount