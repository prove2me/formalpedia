-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_45bc859f_c802_4c58_986e_c045911051ac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:27.608827+00:00
-- url     : https://prove2.me/submissions/e0732479-06c7-401a-a823-c0899c97e5e1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
import Theorems.Thm_SimpleGraph_exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V, G ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K = J := by
  obtain ⟨J, hGJ, hJ, hmax⟩ :=
    SimpleGraph.exists_maximal_supergraph_of_downward_closed__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1
      (P := HasPlanarDrawingOn)
      (by
        intro H K hHK hK
        exact WilliamsonShmoys.planarDrawingOn_mono__p2m_407cedf5_8faa_4a1f_b011_cc5bdf645c63_a1 hHK hK)
      G hDraw
  exact ⟨J, hGJ, hJ, fun K hJK hK => hmax K hJK hK⟩