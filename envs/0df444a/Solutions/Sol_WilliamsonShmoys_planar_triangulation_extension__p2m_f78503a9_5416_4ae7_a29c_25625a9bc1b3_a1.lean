-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_f78503a9_5416_4ae7_a29c_25625a9bc1b3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:09:30.247282+00:00
-- url     : https://prove2.me/submissions/32f443ac-deea-40dd-9c24-227a92826578
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a1
import Theorems.Thm_WilliamsonShmoys_planar_augment_edge__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  let cap : Nat := 3 * Fintype.card V - 6
  have hbound (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
      G.edgeSet.ncard ≤ cap := by
    simpa [cap] using
      WilliamsonShmoys.planar_edge_bound__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a1
        G hG hCard
  have complete :
      ∀ d : Nat, ∀ G : SimpleGraph V, HasPlanarDrawingOn G →
        G.edgeSet.ncard + d = cap →
        ∃ H : SimpleGraph V,
          G ≤ H ∧ HasPlanarDrawingOn H ∧ H.edgeSet.ncard = cap := by
    intro d
    induction d with
    | zero =>
        intro G hG hcount
        exact ⟨G, le_rfl, hG, by simpa using hcount⟩
    | succ d ih =>
        intro G hG hcount
        have hlt : G.edgeSet.ncard < cap := by
          have := hbound G hG
          omega
        obtain ⟨H, hGH, hH, hHcard⟩ :=
          WilliamsonShmoys.planar_augment_edge__p2m_77670b4a_3d82_4709_99a1_b7afb10e3984_a2
            G hG hCard hlt
        have hnext : H.edgeSet.ncard + d = cap := by omega
        obtain ⟨J, hHJ, hJ, hJcard⟩ := ih H hH hnext
        exact ⟨J, le_trans hGH hHJ, hJ, hJcard⟩
  have hboundK := hbound K hK
  have hcount : K.edgeSet.ncard + (cap - K.edgeSet.ncard) = cap := by
    omega
  obtain ⟨L, hKL, hL, hLcard⟩ := complete (cap - K.edgeSet.ncard) K hK hcount
  exact ⟨L, hKL, hL, by simpa [cap] using hLcard.symm⟩