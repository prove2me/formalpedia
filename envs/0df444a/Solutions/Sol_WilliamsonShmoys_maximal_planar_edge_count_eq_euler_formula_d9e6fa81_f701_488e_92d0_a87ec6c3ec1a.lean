-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq_euler_formula_d9e6fa81_f701_488e_92d0_a87ec6c3ec1a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:09:31.597985+00:00
-- url     : https://prove2.me/submissions/5f15cb82-dd79-44c6-ac14-e84894a6d042
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLplanar, hCount⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_with_euler_edge_count_a4f892c9_f19c_464f_8d5c_153cf02f5773
      K hK.1 hCard
  have hLK : L ≤ K := hK.2 L hKL hLplanar
  have hEq : K = L := le_antisymm hKL hLK
  simpa [hEq] using hCount