-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_finite_maximality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:55:42.051615+00:00
-- url     : https://prove2.me/submissions/2058677b-e98f-410b-955e-840b74e98b23

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P →
          WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  classical
  let admissible : Set (SimpleGraph V) :=
    {N | M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
  have hfinite : admissible.Finite := Set.toFinite admissible
  have hnonempty : admissible.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨N, hNmem, hNmax⟩ := hfinite.exists_maximal hnonempty
  change M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N at hNmem
  refine ⟨N, hNmem.1, hNmem.2, ?_⟩
  intro P hNP hP
  have hPadm : admissible P := ⟨le_trans hNmem.1 hNP, hP⟩
  have hPN : P ≤ N := hNmax hPadm hNP
  exact le_antisymm hPN hNP