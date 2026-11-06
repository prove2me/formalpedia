-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:29:16.983034+00:00
-- url     : https://prove2.me/submissions/369e2d79-de37-4155-8246-2d0c63da652f

-- ID: eb4260ba-9d59-4700-a2ea-3c6102b49134 | NAME: WilliamsonShmoys.exists_edge_card_maximal_drawable_extension__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  classical
  let s : Set (SimpleGraph V) := {N | G ≤ N ∧ HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨G, by simp [s, hG]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨K, hKs, hmax⟩ :=
    Set.exists_max_image s (fun N : SimpleGraph V => N.edgeSet.ncard) hsfinite hsne
  have hKs' : G ≤ K ∧ HasPlanarDrawingOn K := by simpa [s] using hKs
  refine ⟨K, hKs'.1, hKs'.2, ?_⟩
  intro L hKL hL
  exact hmax L (by simpa [s] using (show G ≤ L ∧ HasPlanarDrawingOn L from ⟨hKs'.1.trans hKL, hL⟩))
