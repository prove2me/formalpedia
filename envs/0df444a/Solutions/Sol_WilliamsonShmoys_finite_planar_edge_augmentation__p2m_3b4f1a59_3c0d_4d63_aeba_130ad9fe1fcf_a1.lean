-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_edge_augmentation__p2m_3b4f1a59_3c0d_4d63_aeba_130ad9fe1fcf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:44.144077+00:00
-- url     : https://prove2.me/submissions/e8f64bc1-90cc-4c92-ad8f-29c1ea8f17cc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (b : Nat) (hDraw : HasPlanarDrawingOn G)
    (hBound : ∀ H : SimpleGraph V, HasPlanarDrawingOn H → H.edgeSet.ncard ≤ b)
    (hStep : ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H →
      H.edgeSet.ncard < b → ∃ K : SimpleGraph V,
        H ≤ K ∧ K.edgeSet.ncard = H.edgeSet.ncard + 1 ∧ HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧ M.edgeSet.ncard = b := by
  have aux : ∀ n : Nat, ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H →
      H.edgeSet.ncard + n = b →
      ∃ M : SimpleGraph V, H ≤ M ∧ HasPlanarDrawingOn M ∧ M.edgeSet.ncard = b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro H hGH hH hEq
        cases n with
        | zero =>
            refine ⟨H, le_rfl, hH, ?_⟩
            simpa using hEq
        | succ n =>
            have hlt : H.edgeSet.ncard < b := by omega
            obtain ⟨K, hHK, hCard, hK⟩ := hStep H hGH hH hlt
            have hEqK : K.edgeSet.ncard + n = b := by rw [hCard]; omega
            obtain ⟨M, hKM, hM, hMb⟩ := ih n (by omega) K
              (le_trans hGH hHK) hK hEqK
            exact ⟨M, le_trans hHK hKM, hM, hMb⟩
  have hGle : G.edgeSet.ncard ≤ b := hBound G hDraw
  have hEq : G.edgeSet.ncard + (b - G.edgeSet.ncard) = b := by omega
  obtain ⟨M, hGM, hM, hMb⟩ := aux (b - G.edgeSet.ncard) G le_rfl hDraw hEq
  exact ⟨M, hGM, hM, hMb⟩