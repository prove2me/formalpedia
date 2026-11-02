-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_55bcde83_43a5_4c62_ba9b_1744a34b8f86_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:24:17.734856+00:00
-- url     : https://prove2.me/submissions/c7c9e2e0-eef1-4b31-9946-2ee521d1d7ac

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V),
      (∀ [DecidableRel H.Adj],
        G.edgeFinset ⊆ H.edgeFinset ∧
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨H, hGH, _hHdraw, hHcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1
      G hG hcard
  refine ⟨H, ?_⟩
  intro hHdec
  constructor
  · exact SimpleGraph.edgeFinset_mono hGH
  · rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
    exact hHcard
