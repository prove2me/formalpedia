-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_aba97578_a55f_467d_b26f_e953a5f6767e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:24.106104+00:00
-- url     : https://prove2.me/submissions/34583030-e5aa-4ee9-ab94-f158bb9cc1a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
import Theorems.Thm_finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by
  classical
  have hhered : ∀ ⦃A B : SimpleGraph V⦄, B ≤ A → HasPlanarDrawingOn A → HasPlanarDrawingOn B := by
    intro A B hBA hA
    exact WilliamsonShmoys.planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1 B A hBA hA
  have hscore : ∀ A B : SimpleGraph V, A ≤ B → A.edgeSet.ncard ≤ B.edgeSet.ncard := by
    intro A B hAB
    exact Set.ncard_mono (by
      intro e he
      exact SimpleGraph.edgeSet_mono hAB he)
  exact finite_hereditary_maximal_extension__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
    (α := SimpleGraph V) (r := fun A B => A ≤ B)
    (P := HasPlanarDrawingOn) (score := fun A => A.edgeSet.ncard)
    (fun _ => le_rfl)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂)
    (fun _ _ h₁ h₂ => le_antisymm h₁ h₂)
    (fun _ _ h hP => hhered h hP)
    (fun _ _ h => hscore _ _ h)
    G hG