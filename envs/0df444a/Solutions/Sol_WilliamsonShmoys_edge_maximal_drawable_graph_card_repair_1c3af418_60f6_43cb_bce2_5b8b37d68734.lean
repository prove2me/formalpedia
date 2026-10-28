-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_drawable_graph_card_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T08:13:33.977586+00:00
-- url     : https://prove2.me/submissions/ebcd89eb-7d73-4e7c-8ab6-3b7488fecbdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeMaximal_extension_e6e454c7_repair
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_e6e454c7_repair

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hNMax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet → P.edgeSet = N.edgeSet) :
    (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨P, hP, hNP, hPMax⟩ :=
    WilliamsonShmoys.planarDrawingOn_edgeMaximal_extension_e6e454c7_repair N hN
  have hEq : P.edgeSet = N.edgeSet := hNMax P hP hNP
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_e6e454c7_repair
      P hP hPMax hCard
  rw [← hEq]
  have hEulerInt : (Fintype.card V : Int) + (f : Int) =
      (P.edgeSet.ncard : Int) + 2 := by
    exact_mod_cast hEuler
  have hIncidenceInt : 3 * (f : Int) =
      2 * (P.edgeSet.ncard : Int) := by
    exact_mod_cast hIncidence
  nlinarith