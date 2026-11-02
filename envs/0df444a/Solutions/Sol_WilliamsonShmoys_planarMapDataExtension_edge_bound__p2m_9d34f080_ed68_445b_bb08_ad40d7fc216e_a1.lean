-- Prove2me | solution 1 for WilliamsonShmoys.planarMapDataExtension_edge_bound__p2m_9d34f080_ed68_445b_bb08_ad40d7fc216e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:13.221875+00:00
-- url     : https://prove2.me/submissions/85e4e40c-bdad-4236-83fd-454de8c71757

import Definitions.Def_PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (J K : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel K.Adj]
    (hcard : 3 <= Fintype.card V)
    (hsub : forall {u v : V}, J.Adj u v -> K.Adj u v)
    (hdata : Nonempty (PlanarMapData__p2m_b23772a1_7f55_4be6_b745_ebb5a4e685d3_a3 K)) :
    J.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  let d := Classical.choice hdata
  have hsum :
      (Finset.sum Finset.univ (fun _ : Fin d.faceCount => 3)) <=
        Finset.sum Finset.univ (fun f : Fin d.faceCount => d.faceDegree f) := by
    exact Finset.sum_le_sum (fun f _ => d.faceDegree_ge_three f)
  have hdegree : 3 * d.faceCount <= 2 * K.edgeFinset.card := by
    calc
      3 * d.faceCount = Finset.sum Finset.univ (fun _ : Fin d.faceCount => 3) := by simp [Nat.mul_comm]
      _ <= Finset.sum Finset.univ (fun f : Fin d.faceCount => d.faceDegree f) := hsum
      _ = 2 * K.edgeFinset.card := d.sum_faceDegree
  have hK : K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
    nlinarith [d.euler]
  have hsubGraph : J <= K := by
    intro u v huv
    exact hsub huv
  have hEdges : J.edgeFinset.card <= K.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hsubGraph)
  omega