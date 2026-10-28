-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:58:28.684721+00:00
-- url     : https://prove2.me/submissions/3d1880c6-8363-4645-91cc-a542150c4bbe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_set_simpleGraph
import Theorems.Thm_WilliamsonShmoys_exists_maximal_mem_finite_set

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  classical
  let S : Set (SimpleGraph V) :=
    {L | K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L}
  have hS : S.Nonempty := ⟨K, le_rfl, hK⟩
  have hfinite : S.Finite :=
    WilliamsonShmoys.finite_set_simpleGraph S
  obtain ⟨L, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_mem_finite_set S hfinite hS
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hM
  have hML : M ≤ L :=
    hmax M ⟨le_trans hL.1 hLM, hM⟩ hLM
  exact le_antisymm hML hLM