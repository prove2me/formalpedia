-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:21:51.322896+00:00
-- url     : https://prove2.me/submissions/63251f93-3353-4703-ad5b-06c14eee4586

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
import Theorems.Thm_WilliamsonShmoys_planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hdec, hHK, hKplanar, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
      H hcard hH
  letI : DecidableRel K.Adj := hdec
  have hle := WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
    H K hHK
  have hcount := WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
    K hcard hKplanar hmax
  exact ⟨K, inferInstance, hHK, hle, hcount⟩