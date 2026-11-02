-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_62655122_fd0a_4865_bebb_51bfbf1c6569_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:02.024028+00:00
-- url     : https://prove2.me/submissions/ce21f2fe-d03a-4be4-91fc-ae3d18b19f87

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ M' : SimpleGraph V, HasPlanarDrawingOn M' ∧ M ≤ M' ∧
      ∀ N : SimpleGraph V, HasPlanarDrawingOn N → M' ≤ N → N = M' := by
  classical
  let p : SimpleGraph V → Prop := fun N => HasPlanarDrawingOn N ∧ M ≤ N
  obtain ⟨M', hMM', hmax⟩ :=
    Finite.exists_le_maximal (p := p) (a := M) ⟨hM, le_rfl⟩
  refine ⟨M', hmax.1.1, hMM', ?_⟩
  intro N hN hM'N
  have hNp : p N := ⟨hN, hMM'.trans hM'N⟩
  have hNM' : N ≤ M' := hmax.2 hNp hM'N
  exact le_antisymm hNM' hM'N