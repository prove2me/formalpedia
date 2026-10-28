-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_exists_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:58:06.640261+00:00
-- url     : https://prove2.me/submissions/e9211fe8-6db5-4d05-bb73-70365da36048

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_planar_extension_20261026
import Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite_set_planar_extension_20261026

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V,
      K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
        ∀ L : SimpleGraph V, J ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = J := by
  let S : Set (SimpleGraph V) := {J | K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}
  have hS : S.Nonempty := ⟨K, by simp [S, hK]⟩
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.finite_simpleGraph_planar_extension_20261026 (V := V)
  obtain ⟨J, hJ, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_element_of_finite_set_planar_extension_20261026 S hS
  change K ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J at hJ
  refine ⟨J, hJ.1, hJ.2, ?_⟩
  intro L hJL hL
  have hLmem : L ∈ S := ⟨le_trans hJ.1 hJL, hL⟩
  exact hmax L hJL hLmem