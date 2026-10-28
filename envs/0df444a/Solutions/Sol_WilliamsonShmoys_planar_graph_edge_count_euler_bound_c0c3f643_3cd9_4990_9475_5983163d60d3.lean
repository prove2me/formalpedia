-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:48:14.944496+00:00
-- url     : https://prove2.me/submissions/3396778e-0628-4842-9caa-557ab8298682

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
      (H : SimpleGraph V)
      (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
      (hCard : 3 ≤ Fintype.card V),
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6) := by
  intro h
  let G : SimpleGraph (Fin 3) := ⊥
  have hG : WilliamsonShmoys.HasPlanarDrawingOn G := by
    refine ⟨fun v => ((v.val : ℝ), (0 : ℝ)), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro a b hab
      apply Fin.ext
      have hfst : (a.val : ℝ) = (b.val : ℝ) := by
        simpa using congrArg Prod.fst hab
      exact Nat.cast_injective hfst
    · intro u v huv hadj
      simp [G] at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp [G] at hadj₁
  have hCard : 3 ≤ Fintype.card (Fin 3) := by simp
  have hBound := h (V := Fin 3) G hG hCard
  norm_num [G] at hBound