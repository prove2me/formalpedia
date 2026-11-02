-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_instance_irrel__p2m_160c891e_c18d_4863_b495_0a238ee51219_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:54.649554+00:00
-- url     : https://prove2.me/submissions/d905d6d6-259d-40b1-9be5-547dbe44e7a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     G.edgeFinset.card) =
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := G.fintypeEdgeSet
     G.edgeFinset.card) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hfin :
      (letI : Fintype ↑G.edgeSet := Fintype.ofFinite _; G.edgeFinset) =
      (letI : Fintype ↑G.edgeSet := G.fintypeEdgeSet; G.edgeFinset) := by
    apply Finset.ext
    intro e
    simp [SimpleGraph.edgeFinset]
  exact congrArg Finset.card hfin