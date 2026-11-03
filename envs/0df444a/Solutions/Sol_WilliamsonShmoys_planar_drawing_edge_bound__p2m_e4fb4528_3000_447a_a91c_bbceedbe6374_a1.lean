-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_edge_bound__p2m_e4fb4528_3000_447a_a91c_bbceedbe6374_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:35.270416+00:00
-- url     : https://prove2.me/submissions/9b959df9-e917-4f78-9d02-620fce8af24b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  obtain ⟨M, hHM, hM, hMax, hcard_le⟩ :=
    WilliamsonShmoys.maximal_planar_completion_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
      H hH
  have hM_eq :=
    WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound__p2m_55c0bceb_ffb6_44c6_a362_90e494710496_a2
      M hM hMax hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  omega
