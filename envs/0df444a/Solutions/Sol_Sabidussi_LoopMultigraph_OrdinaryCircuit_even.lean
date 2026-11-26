-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.OrdinaryCircuit.even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:14.971127+00:00
-- url     : https://prove2.me/submissions/7acab35b-ae67-408f-bff8-d4d143bce6ec

import Definitions.Def_Sabidussi_LoopGraphBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_Sabidussi_OrdinaryCircuit

set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
namespace Sabidussi.LoopMultigraph
namespace OrdinaryCircuit
theorem _root_.solution (C : G.OrdinaryCircuit) : G.IsEvenEdgeSet C.edges := by
  rw [G.isEvenEdgeSet_iff_even_degree]
  intro v
  by_cases hv : v ∈ G.edgeSupport C.edges
  · rw [C.twoRegular v hv]
    exact ⟨1, by omega⟩
  · have hnpos : ¬ 0 < G.degreeIn C.edges v := by
      intro hp
      exact hv ((G.degreeIn_pos_iff_mem_edgeSupport C.edges v).mp hp)
    have hz : G.degreeIn C.edges v = 0 := Nat.eq_zero_of_not_pos hnpos
    rw [hz]
    exact Even.zero
end OrdinaryCircuit
end Sabidussi.LoopMultigraph
