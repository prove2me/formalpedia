-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_1076f7d9_8cab_4c50_ba02_63cd640503d2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:01.674158+00:00
-- url     : https://prove2.me/submissions/2f6db8f0-9a6c-4ab4-8f2f-1a2c6ababe0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  let B : Nat := 3 * Fintype.card V
  have hBound :
      M.edgeSet.ncard + 6 ≤ B :=
    WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
      M hV hDraw
  have hComplete :
      ∀ d : Nat, ∀ G : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn G →
        G.edgeSet.ncard + 6 + d = B →
        ∃ N : SimpleGraph V,
          G.edgeSet ⊆ N.edgeSet ∧
          WilliamsonShmoys.HasPlanarDrawingOn N ∧
          N.edgeSet.ncard + 6 = B := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro G hG hEq
      by_cases hz : d = 0
      · subst d
        refine ⟨G, Set.Subset.rfl, hG, ?_⟩
        simpa [B] using hEq
      · have hd : 0 < d := Nat.pos_of_ne_zero hz
        have hLt : G.edgeSet.ncard + 6 < B := by omega
        obtain ⟨H, hGH, hH, hStep⟩ :=
          WilliamsonShmoys.planar_drawing_add_edge__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
            G hV hG hLt
        have hEq'' : H.edgeSet.ncard + 6 + (d - 1) = B := by
          rw [hStep]
          omega
        obtain ⟨N, hHN, hN, hFinal⟩ :=
          ih (d - 1) (by omega) H hH hEq''
        exact ⟨N, Set.Subset.trans hGH hHN, hN, hFinal⟩
  let d : Nat := B - (M.edgeSet.ncard + 6)
  have hEq : M.edgeSet.ncard + 6 + d = B := by
    dsimp [d]
    omega
  obtain ⟨N, hMN, hN, hFinal⟩ := hComplete d M hDraw hEq
  exact ⟨N, hMN, hN, by simpa [B] using hFinal⟩