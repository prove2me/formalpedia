-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_strict_extension_below_max_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:59:37.979556+00:00
-- url     : https://prove2.me/submissions/9ecf4b57-1ad9-4583-ba5e-4150cefc8411

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_9f4db670
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_9f4db670

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : (G.edgeSet.ncard : Int) < 3 * (Fintype.card V : Int) - 6) :
    ∃ L : SimpleGraph V,
      G.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hsub, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_9f4db670 G hG
  have hLcount :=
    WilliamsonShmoys.maximal_planar_edge_count_9f4db670 L hL hMax hCard
  have hneq : G.edgeSet ≠ L.edgeSet := by
    intro hEq
    have hCounts : (G.edgeSet.ncard : Int) = (L.edgeSet.ncard : Int) :=
      congrArg (fun E : Set (Sym2 V) => (E.ncard : Int)) hEq
    omega
  have hproper : G.edgeSet ⊂ L.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, hneq⟩
  exact ⟨L, hproper, hL⟩