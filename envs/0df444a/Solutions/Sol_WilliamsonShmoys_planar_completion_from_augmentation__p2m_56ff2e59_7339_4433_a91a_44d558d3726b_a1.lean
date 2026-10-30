-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_from_augmentation__p2m_56ff2e59_7339_4433_a91a_44d558d3726b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:56:22.822926+00:00
-- url     : https://prove2.me/submissions/596ed643-2e70-4091-a5bb-0230063f1b60

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hAug : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G →
      G.edgeSet.ncard + 6 < 3 * Fintype.card V →
      ∃ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet ⊆ H.edgeSet ∧ H.edgeSet.ncard = G.edgeSet.ncard + 1) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hKbound :
      K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
      K hK hV
  have aux :
      ∀ d : ℕ, ∀ G : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn G →
        K.edgeSet ⊆ G.edgeSet →
        G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V →
        3 * Fintype.card V - (G.edgeSet.ncard + 6) = d →
        ∃ L : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn L ∧
          K.edgeSet ⊆ L.edgeSet ∧
          L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro G hG hKG hBound hdiff
        by_cases heq : G.edgeSet.ncard + 6 = 3 * Fintype.card V
        · exact ⟨G, hG, hKG, heq⟩
        · have hlt : G.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
          obtain ⟨H, hH, hGH, hHcount⟩ := hAug G hG hlt
          have hHbound :
              H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
            WilliamsonShmoys.planar_edge_count_le__p2m_bd86803d_f791_454d_9e3d_cf8ce9ce0da0_a1
              H hH hV
          have hdiffH :
              3 * Fintype.card V - (H.edgeSet.ncard + 6) = d - 1 := by
            rw [hHcount]
            omega
          have hdecrease : d - 1 < d := by omega
          obtain ⟨L, hL, hHL, hLeq⟩ :=
            ih (d - 1) hdecrease H hH (Set.Subset.trans hKG hGH)
              hHbound hdiffH
          exact ⟨L, hL, hHL, hLeq⟩
  exact aux (3 * Fintype.card V - (K.edgeSet.ncard + 6))
    K hK (Set.Subset.rfl) hKbound rfl
