-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:24.706701+00:00
-- url     : https://prove2.me/submissions/43e05e94-1915-47f8-986a-bb37342aeb13

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by
  classical
  let p : SimpleGraph V → Prop := fun G => H ≤ G ∧ HasPlanarDrawingOn G
  have hp : p H := ⟨le_rfl, hH⟩
  obtain ⟨K, dK, hExt⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).2 ⟨H, hp⟩
  letI := dK
  rcases hExt.1 with ⟨hHK, hdrawK⟩
  refine ⟨K, hHK, hdrawK, ?_⟩
  intro L hKL hdrawL
  have hPL : p L := ⟨hHK.trans hKL, hdrawL⟩
  exact ((SimpleGraph.IsExtremal.le_iff_eq (G := K) (p := p) hExt hPL).1 hKL).symm