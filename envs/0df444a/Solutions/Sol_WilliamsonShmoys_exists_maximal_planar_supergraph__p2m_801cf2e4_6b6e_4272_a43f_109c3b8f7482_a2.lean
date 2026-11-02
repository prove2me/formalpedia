-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_801cf2e4_6b6e_4272_a43f_109c3b8f7482_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:23.552844+00:00
-- url     : https://prove2.me/submissions/ef5f3dac-a8da-4b07-a1b4-a0322c517e6d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v := by
  classical
  let P : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hP : ∃ G, P G := ⟨H, le_rfl, hH⟩
  obtain ⟨K, hK, hmax⟩ :=
    exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1
      (α := SimpleGraph V) (R := fun A B => A ≤ B) P
      (fun _ => le_rfl) (fun _ _ _ hab hbc => le_trans hab hbc) hP
  refine ⟨K, ?_, hK.2, ?_⟩
  · exact hK.1
  · intro L hKL hL u v huv
    have hLK : L ≤ K := hmax L ⟨le_trans hK.1 hKL, hL⟩ hKL
    exact hLK huv