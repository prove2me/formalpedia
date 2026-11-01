-- Prove2me | solution 1 for WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:01:38.587442+00:00
-- url     : https://prove2.me/submissions/9576f7f6-bffa-44d0-8993-c5b0aac9423c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_planar_supergraph__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
import Theorems.Thm_maximal_planar_edge_count__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
import Theorems.Thm_planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G ≤ K ∧
      K.edgeFinset.card = G.edgeFinset.card + 1 := by
  obtain ⟨M, dM, hM, hGM, hMax⟩ :=
    exists_maximal_planar_supergraph__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
      G dG hG
  have hMcard :=
    maximal_planar_edge_count__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
      M dM hM hV hMax
  have hlt : G.edgeFinset.card < M.edgeFinset.card := by omega
  exact
    planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
      G M dG dM hG hM hGM hlt