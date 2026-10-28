-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_at_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:31:18.893971+00:00
-- url     : https://prove2.me/submissions/444616d8-ab86-4057-a2d0-1235064655c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  let target : ℕ := 3 * Fintype.card V - 6
  have finish : ∀ k (G : SimpleGraph V),
      G.edgeSet.ncard + k = target →
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ∃ N : SimpleGraph V, G ≤ N ∧
        WilliamsonShmoys.HasPlanarDrawingOn N ∧ N.edgeSet.ncard = target := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro G hcount hdraw
      by_cases hk : k = 0
      · subst k
        have heq : G.edgeSet.ncard = target := by omega
        exact ⟨G, le_rfl, hdraw, heq⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hlt : G.edgeSet.ncard < target := by omega
        obtain ⟨G', hGG', hdraw', hstep⟩ :=
          WilliamsonShmoys.planar_edge_augmentation G hV hdraw hlt
        have hcount' : G'.edgeSet.ncard + (k - 1) = target := by omega
        obtain ⟨N, hG'N, hdrawN, hN⟩ :=
          ih (k - 1) (by omega) G' hcount' hdraw'
        exact ⟨N, le_trans hGG' hG'N, hdrawN, hN⟩
  have hbound : M.edgeSet.ncard ≤ target := by
    dsimp [target]
    exact WilliamsonShmoys.planar_edge_bound M hV hM
  obtain ⟨N, hMN, hdrawN, hN⟩ :=
    finish (target - M.edgeSet.ncard) M (by omega) hM
  exact ⟨N, hMN, hdrawN, by simpa [target] using hN⟩