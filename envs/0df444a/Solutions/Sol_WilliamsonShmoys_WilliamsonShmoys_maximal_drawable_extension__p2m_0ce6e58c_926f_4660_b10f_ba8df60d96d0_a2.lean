-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_maximal_drawable_extension__p2m_0ce6e58c_926f_4660_b10f_ba8df60d96d0_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:56.414477+00:00
-- url     : https://prove2.me/submissions/9a39db9d-49d1-4139-bb13-1f9e9b94b4df

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
import Theorems.Thm_WilliamsonShmoys_exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q := by
  exact WilliamsonShmoys.exists_maximal_good_supergraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
    P HasPlanarDrawingOn hP
    (by
      intro G H hHG hG
      exact WilliamsonShmoys.planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2 hHG hG)