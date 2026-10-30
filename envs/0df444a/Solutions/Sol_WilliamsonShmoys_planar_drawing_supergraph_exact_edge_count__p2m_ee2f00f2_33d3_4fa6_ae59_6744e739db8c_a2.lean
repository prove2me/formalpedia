-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count__p2m_ee2f00f2_33d3_4fa6_ae59_6744e739db8c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:30:07.528926+00:00
-- url     : https://prove2.me/submissions/22c4c088-3484-4af1-a281-00ca84b7fab4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
import Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  classical
  let m : ℕ := 3 * Fintype.card V - 6
  have hm : G.edgeSet.ncard ≤ m :=
    WilliamsonShmoys.planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
      G hDraw hCard
  have hstep :
      ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard < m →
        ∃ L : SimpleGraph V,
          K.edgeSet ⊆ L.edgeSet ∧
          L.edgeSet.ncard = K.edgeSet.ncard + 1 ∧
          WilliamsonShmoys.HasPlanarDrawingOn L := by
    intro K hK hKm
    exact WilliamsonShmoys.planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
      K hK hCard (by simpa [m] using hKm)
  obtain ⟨H, hsub, hcount, hPlanar⟩ :=
    WilliamsonShmoys.finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
      (fun K : SimpleGraph V => WilliamsonShmoys.HasPlanarDrawingOn K)
      G m hDraw hm hstep
  exact ⟨H, hsub, Set.ncard_mono hsub, by simpa [m] using hcount, hPlanar⟩
