-- Prove2me | solution 1 for QEC.Coding.BDL26BaseGeometricDomain.tanner_z_in_incoming_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:47:41.116195+00:00
-- url     : https://prove2.me/submissions/bcf89a80-c6ec-4596-b354-e74769cb4e75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph

set_option autoImplicit false
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26FiniteTannerSquare QEC.Coding.BDL26DecodingGraph
open scoped Classical

namespace QEC.Coding.BDL26BaseGeometricDomain
theorem _root_.solution (P : TannerSquarePresentation)
    (z : P.Z) (v : Vertex P) (radius : Nat) :
    Vertex.z z ∈ LocalRegion.directedNeighborhood (tannerLevel P).graph v radius ↔
      Vertex.z z=v := by
  have distanceFromTerminal {V : Type} [Fintype V] [DecidableEq V]
      (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false) (v : V) :
      G.distance u v=(if u=v then 0 else ⊤) := by
    have hreach : ∀ steps, G.reachableWithin steps u v=decide (u=v) := by
      intro steps
      induction steps with
      | zero => rfl
      | succ steps ih =>
        simp [DirectedGraph.reachableWithin,ih,hu]
    have haux : ∀ steps, G.distanceAux u v steps=(if u=v then some 0 else none) := by
      intro steps
      induction steps with
      | zero => simp [DirectedGraph.distanceAux,hreach]
      | succ steps ih =>
        rw [DirectedGraph.distanceAux,ih]
        by_cases he : u=v
        · simp only [if_pos he]
        · simp only [if_neg he,hreach,decide_eq_true_eq]
    simp only [DirectedGraph.distance,haux]
    by_cases he : u=v <;> simp [he]
  have terminalIncoming {V : Type} [Fintype V] [DecidableEq V]
      (G : DirectedGraph V) (u : V) (hu : ∀ w, G.edge u w=false)
      (v : V) (radius : Nat) :
      u ∈ LocalRegion.directedNeighborhood G v radius ↔ u=v := by
    simp only [LocalRegion.directedNeighborhood,Finset.mem_filter,
      Finset.mem_univ,true_and]
    rw [distanceFromTerminal G u hu v]
    by_cases he : u=v <;> simp [he]
  apply terminalIncoming
  intro w
  rw [tannerLevel_edge]
  cases w <;> rfl
end QEC.Coding.BDL26BaseGeometricDomain
