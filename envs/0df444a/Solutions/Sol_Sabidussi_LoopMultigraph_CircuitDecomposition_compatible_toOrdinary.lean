-- Prove2me | solution 1 for Sabidussi.LoopMultigraph.CircuitDecomposition.compatible_toOrdinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:55.068005+00:00
-- url     : https://prove2.me/submissions/f9d86a07-4676-4bae-8f8d-706e9d78c7bd

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
namespace CircuitDecomposition
theorem _root_.solution {T : G.EulerTour}
    {S : G.CircuitDecomposition} (h : S.Compatible T) : S.toOrdinary.Compatible T := by
  intro i C hC
  change C ∈ S.circuits.map (Cycle.toOrdinaryCircuit G) at hC
  rw [List.mem_map] at hC
  obtain ⟨D, hD, rfl⟩ := hC
  exact h i D hD
end CircuitDecomposition
end Sabidussi.LoopMultigraph
