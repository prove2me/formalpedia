-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_76432751_4a60_438b_af25_c322d55d602e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:39:10.652662+00:00
-- url     : https://prove2.me/submissions/984dff3f-fab1-4b71-8c82-4a66f4cb4933

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel K.Adj := dK
       WilliamsonShmoys.HasPlanarDrawingOn K →
       H.edgeFinset ⊆ K.edgeFinset →
       K.edgeFinset ⊆ H.edgeFinset)) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨K, dK, hKplanar, hKdata⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_extension__p2m_3bd27e40_28f0_4f6f_8869_04bf87b1e140_a1
      H hH hV
  letI : DecidableRel K.Adj := dK
  rcases hKdata with ⟨hsub, hcard⟩
  have hsup := hmax K dK hKplanar hsub
  have heq : H.edgeFinset = K.edgeFinset :=
    Finset.Subset.antisymm hsub hsup
  simpa [heq] using hcard