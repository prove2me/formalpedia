-- Prove2me | solution 1 for WilliamsonShmoys.exists_drawable_maximal_supergraph__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:53.489085+00:00
-- url     : https://prove2.me/submissions/56a73004-96d3-46d9-8489-18e00efd69ff

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  let P : SimpleGraph V → Prop := fun G => J ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G
  have hJ : P J := ⟨le_rfl, hDraw⟩
  obtain ⟨K, hJK, hKmax⟩ :=
    (inferInstance : Finite (SimpleGraph V)).exists_le_maximal (p := P) hJ
  refine ⟨K, hJK, hKmax.1.2, ?_⟩
  intro L hKL hLDraw
  have hPL : P L := ⟨hJK.trans hKL, hLDraw⟩
  exact (hKmax.eq_of_le hPL hKL).symm