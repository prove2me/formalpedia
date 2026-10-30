-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_c4011bda_e2a2_4391_a47d_b4ea4febecd9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:24:14.599397+00:00
-- url     : https://prove2.me/submissions/2df2e4c5-28fc-4b05-a1ec-89203820acd5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨T, hLT, hT, hcount⟩ :=
    WilliamsonShmoys.exists_triangulation_supergraph_for_edge_count_c4011bda_e2a2_4391_a47d_b4ea4febecd9 L hL hCard
  have hTL : T = L := hMax T hLT hT
  subst T
  omega
