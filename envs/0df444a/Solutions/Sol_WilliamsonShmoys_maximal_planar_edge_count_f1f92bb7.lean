-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_f1f92bb7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:01:51.251498+00:00
-- url     : https://prove2.me/submissions/eee30e59-12db-4153-ba11-5ce320924ff0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_extension_f1f92bb7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨M, hsub, hM, hcount⟩ :=
    WilliamsonShmoys.drawable_triangulation_extension_f1f92bb7 L hL hCard
  have heq : M = L := hMax M hsub hM
  rw [heq] at hcount
  exact hcount.symm