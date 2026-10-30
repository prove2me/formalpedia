-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_face_count_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:44:46.159992+00:00
-- url     : https://prove2.me/submissions/527eae0a-abbe-4d89-939d-106cd5d5dc75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_same_vertex

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card V = n) :
    ∃ f : Nat,
      n + f = L.edgeSet.ncard + 2 ∧
      2 * L.edgeSet.ncard = 3 * f := by
  have hCard : 3 ≤ Fintype.card V := by omega
  obtain ⟨M, hLM, hMdraw, hMedges⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph_same_vertex
      L hDrawing hCard
  have hML : M ≤ L := hMax M hLM hMdraw
  have hEq : M = L := le_antisymm hML hLM
  rw [hEq] at hMedges
  refine ⟨2 * n - 4, ?_, ?_⟩ <;> omega