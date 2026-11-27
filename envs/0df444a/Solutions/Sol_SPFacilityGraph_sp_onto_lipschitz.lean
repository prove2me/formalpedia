-- Prove2me | solution 1 for SPFacilityGraph.sp_onto_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:56:10.002864+00:00
-- url     : https://prove2.me/submissions/50eade9b-498b-45ef-8e7c-c34a0a77a55a

import Mathlib
import Theorems.Thm_SPFacilityGraph_sp_onto_gate
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm

set_option autoImplicit false

open SPFacilityGraph

theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n) (i : Fin n) (y : G.Pt) :
    G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i) := by
  have e0 : Function.update x i (x i) = x := Function.update_eq_self i x
  have g1 := sp_onto_gate hn G M hSP hM x i y (x i)
  have g2 := sp_onto_gate hn G M hSP hM x i (x i) y
  rw [e0] at g1 g2
  have t1 := G.dist_triangle y (x i) (M x)
  have t2 := G.dist_triangle (x i) y (M (Function.update x i y))
  rw [G.dist_comm (M x) (M (Function.update x i y))] at g2
  rw [G.dist_comm (x i) y] at t2
  linarith
