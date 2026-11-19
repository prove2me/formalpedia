-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:32:09.761795+00:00
-- url     : https://prove2.me/submissions/4b17a763-e1cb-4281-a6bb-1214cd2adafb

import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_gadget_graph_properties
import Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_gadget_coherent_simulation

open QuantumBipartiteTesting.Bipartiteness

theorem solution :
    (∀ n : ℕ, ∀ F : Finset (ColoredEdge n), Consistent F → ∀ b : ColoredEdge n → Bool,
      IsGraph (Gadget F b) ∧ DegreeBound 3 (Gadget F b) ∧
      (Bipartite (Gadget F b) ↔ Balanced F b) ∧
      DeletionDistance (Gadget F b) = Frustration F b ∧
      EditDistance (Gadget F b) = Frustration F b) ∧
    (∃ K : ℕ, CoherentSimulation K) := by
  exact ⟨gadget_graph_properties,6,gadget_coherent_simulation⟩
