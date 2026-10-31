-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:17.943025+00:00
-- url     : https://prove2.me/submissions/8411d840-3608-4469-923b-5aaf26992040

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
      K hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_219a8e3b_c7d8_43b3_9ee1_a4b3ebf8e3f2_a1
      L hL hV hMax
  exact ⟨L, hKL, hL, hCount.symm.le⟩