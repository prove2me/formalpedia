-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:18.357168+00:00
-- url     : https://prove2.me/submissions/18d09999-f2b7-4ad7-887d-1785dae193c1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V <= L.edgeFinset.card + 6 := by
  classical
  have hex :=
    WilliamsonShmoys.drawable_graph_has_triangulation_extension__p2m_5f13f5bc_06ce_43c4_9feb_29baebe6cd36_a2
      L hL hcard
  let M := Classical.choose hex
  have hdecEx := Classical.choose_spec hex
  let hDec : DecidableRel M.Adj := Classical.choose hdecEx
  letI : DecidableRel M.Adj := hDec
  have hparts := Classical.choose_spec hdecEx
  have hLM : L <= M := hparts.1
  have hrest := hparts.2
  have hM : HasPlanarDrawingOn M := hrest.1
  have hcount : 3 * Fintype.card V = M.edgeFinset.card + 6 := hrest.2
  have hEq : M = L := hmax M hLM hM
  have hEdges : M.edgeFinset = L.edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset, hEq]
  have hcardEdges : M.edgeFinset.card = L.edgeFinset.card :=
    congrArg Finset.card hEdges
  omega
