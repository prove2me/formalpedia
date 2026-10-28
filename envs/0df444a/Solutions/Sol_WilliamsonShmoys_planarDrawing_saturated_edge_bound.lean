-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_saturated_edge_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:51:26.314772+00:00
-- url     : https://prove2.me/submissions/42b1b45b-889d-4b4b-bbbe-4943e64da4de

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V],
      (P : SimpleGraph V) →
      HasPlanarDrawingOn P →
      3 ≤ Fintype.card V →
      (∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q →
        P.edgeSet.ncard ≤ Q.edgeSet.ncard) →
      3 * Fintype.card V ≤ P.edgeSet.ncard + 6) := by
  intro h
  let P : SimpleGraph (Fin 3) := ⊥
  have hPlanar : HasPlanarDrawingOn P := by
    dsimp [P]
    refine ⟨fun i => ((i : ℝ), (0 : ℝ)), (fun _ _ _ => (0, 0)), ?_, ?_, ?_⟩
    · intro a b hab
      apply Fin.ext
      have hh : (a : ℝ) = (b : ℝ) := congrArg Prod.fst hab
      exact_mod_cast hh
    · intro u v huv hadj
      simp at hadj
    · intro u v x y huv hxy hadj₁ hadj₂ hne t ht s hs heq
      simp at hadj₁
  have hMax : ∀ Q : SimpleGraph (Fin 3), P ≤ Q → HasPlanarDrawingOn Q →
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
    intro Q hPQ hQ
    simpa [P] using (Nat.zero_le Q.edgeSet.ncard)
  have hCard : 3 ≤ Fintype.card (Fin 3) := by simp
  have hBound := h P hPlanar hCard hMax
  norm_num [P] at hBound