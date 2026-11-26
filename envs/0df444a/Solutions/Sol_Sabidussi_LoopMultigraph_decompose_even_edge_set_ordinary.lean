-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.decompose_even_edge_set_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:20.831586+00:00
-- url     : https://prove2.me/submissions/69eab808-876f-427b-862c-cb6f1e3f3f12

import Definitions.Def_Sabidussi_LoopGraphBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_Sabidussi_OrdinaryCircuit
import Theorems.Thm_Sabidussi_LoopMultigraph_decompose_even_edge_set


set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
namespace Sabidussi.LoopMultigraph
theorem _root_.solution (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.OrdinaryCircuit,
      ∀ e : E, (L.filter fun C ↦ e ∈ C.edges).length = if e ∈ F then 1 else 0 := by
  obtain ⟨L, hL⟩ := G.decompose_even_edge_set F hF
  refine ⟨L.map (Cycle.toOrdinaryCircuit G), ?_⟩
  intro e
  rw [filter_map_toOrdinaryCircuit_length, hL e]
end Sabidussi.LoopMultigraph
