-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_strict_supergraph_of_not_connected_with_three_vertices__p2m_bc735298_99fb_476e_aa8d_1e3af7f2e774_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:40.684746+00:00
-- url     : https://prove2.me/submissions/539fdc1c-f2c5-4781-ab8c-586c658f16ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
import Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKplanar : HasPlanarDrawingOn K)
    (hnot : ¬ K.Connected) (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧ K.edgeSet.ncard < L.edgeSet.ncard := by
  obtain ⟨L, hKL, hLplanar, hLmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
      K hKplanar
  have hLconn : L.Connected :=
    WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
      L hLplanar hV hLmax
  have hKneL : K ≠ L := by
    intro h
    subst L
    exact hnot hLconn
  exact ⟨L, hKL, hLplanar,
    WilliamsonShmoys.strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
      K L hKL hKneL⟩